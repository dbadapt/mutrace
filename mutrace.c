/*-*- Mode: C; c-basic-offset: 8 -*-*/

/***
  This file is part of mutrace.

  Copyright 2009 Lennart Poettering

  mutrace is free software: you can redistribute it and/or modify it
  under the terms of the GNU Lesser General Public License as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  mutrace is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with mutrace. If not, see <http://www.gnu.org/licenses/>.
***/

#include "config.h"

#include <pthread.h>
#include <execinfo.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>
#include <dlfcn.h>
#include <stdbool.h>
#include <errno.h>
#include <string.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <sys/prctl.h>
#include <sched.h>
#include <malloc.h>

#if !defined (__linux__) || !defined(__GLIBC__)
#error "This stuff only works on Linux!"
#endif

#ifndef SCHED_RESET_ON_FORK
/* "Your libc lacks the definition of SCHED_RESET_ON_FORK. We'll now
 * define it ourselves, however make sure your kernel is new
 * enough! */
#define SCHED_RESET_ON_FORK 0x40000000
#endif

#if defined(__i386__) || defined(__x86_64__)
#define DEBUG_TRAP __asm__("int $3")
#else
#include <signal.h>
#define DEBUG_TRAP raise(SIGTRAP)
#endif

#define LIKELY(x) (__builtin_expect(!!(x),1))
#define UNLIKELY(x) (__builtin_expect(!!(x),0))

struct mutex_info {
        pthread_mutex_t *mutex;
        pthread_rwlock_t *rwlock;

        int type, protocol, kind;
        bool broken:1;
        bool realtime:1;
        bool dead:1;

        unsigned n_lock_level;

        pid_t last_owner;

        unsigned n_locked;
        unsigned n_owner_changed;
        unsigned n_contended;

        uint64_t nsec_locked_total;
        uint64_t nsec_locked_max;

        uint64_t nsec_timestamp;
        char *stacktrace;

        unsigned id;

        struct mutex_info *next;
};

static unsigned hash_size = 3371; /* probably a good idea to pick a prime here */
static unsigned frames_max = 16;

static volatile unsigned n_broken = 0;
static volatile unsigned n_collisions = 0;
static volatile unsigned n_self_contended = 0;

static unsigned show_n_locked_min = 1;
static unsigned show_n_owner_changed_min = 2;
static unsigned show_n_contended_min = 0;
static unsigned show_n_max = 10;

static bool raise_trap = false;
static bool track_rt = false;

static int (*real_pthread_mutex_init)(pthread_mutex_t *mutex, const pthread_mutexattr_t *mutexattr) = NULL;
static int (*real_pthread_mutex_destroy)(pthread_mutex_t *mutex) = NULL;
static int (*real_pthread_mutex_lock)(pthread_mutex_t *mutex) = NULL;
static int (*real_pthread_mutex_trylock)(pthread_mutex_t *mutex) = NULL;
static int (*real_pthread_mutex_timedlock)(pthread_mutex_t *mutex, const struct timespec *abstime) = NULL;
static int (*real_pthread_mutex_unlock)(pthread_mutex_t *mutex) = NULL;
static int (*real_pthread_cond_wait)(pthread_cond_t *cond, pthread_mutex_t *mutex) = NULL;
static int (*real_pthread_cond_timedwait)(pthread_cond_t *cond, pthread_mutex_t *mutex, const struct timespec *abstime) = NULL;
static int (*real_pthread_create)(pthread_t *newthread, const pthread_attr_t *attr, void *(*start_routine) (void *), void *arg) = NULL;
static int (*real_pthread_rwlock_init)(pthread_rwlock_t *rwlock, const pthread_rwlockattr_t *attr) = NULL;
static int (*real_pthread_rwlock_destroy)(pthread_rwlock_t *rwlock) = NULL;
static int (*real_pthread_rwlock_rdlock)(pthread_rwlock_t *rwlock) = NULL;
static int (*real_pthread_rwlock_tryrdlock)(pthread_rwlock_t *rwlock) = NULL;
static int (*real_pthread_rwlock_timedrdlock)(pthread_rwlock_t *rwlock, const struct timespec *abstime) = NULL;
static int (*real_pthread_rwlock_wrlock)(pthread_rwlock_t *rwlock) = NULL;
static int (*real_pthread_rwlock_trywrlock)(pthread_rwlock_t *rwlock) = NULL;
static int (*real_pthread_rwlock_timedwrlock)(pthread_rwlock_t *rwlock, const struct timespec *abstime) = NULL;
static int (*real_pthread_rwlock_unlock)(pthread_rwlock_t *rwlock);
static void (*real_exit)(int status) __attribute__((noreturn)) = NULL;
static void (*real__exit)(int status) __attribute__((noreturn)) = NULL;
static void (*real__Exit)(int status) __attribute__((noreturn)) = NULL;
static int (*real_backtrace)(void **array, int size) = NULL;
static char **(*real_backtrace_symbols)(void *const *array, int size) = NULL;
static void (*real_backtrace_symbols_fd)(void *const *array, int size, int fd) = NULL;

static struct mutex_info **alive_mutexes = NULL, **dead_mutexes = NULL;
static pthread_mutex_t *mutexes_lock = NULL;

static __thread bool recursive = false;

static volatile bool initialized = false;
static volatile bool threads_existing = false;

static uint64_t nsec_timestamp_setup;

static void setup(void) __attribute ((constructor));
static void shutdown(void) __attribute ((destructor));

static pid_t _gettid(void) {
        return (pid_t) syscall(SYS_gettid);
}

static uint64_t nsec_now(void) {
        struct timespec ts;
        int r;

        r = clock_gettime(CLOCK_MONOTONIC, &ts);
        assert(r == 0);

        return
                (uint64_t) ts.tv_sec * 1000000000ULL +
                (uint64_t) ts.tv_nsec;
}

static const char *get_prname(void) {
        static char prname[17];
        int r;

        r = prctl(PR_GET_NAME, prname);
        assert(r == 0);

        prname[16] = 0;

        return prname;
}

static int parse_env(const char *n, unsigned *t) {
        const char *e;
        char *x = NULL;
        unsigned long ul;

        if (!(e = getenv(n)))
                return 0;

        errno = 0;
        ul = strtoul(e, &x, 0);
        if (!x || *x || errno != 0)
                return -1;

        *t = (unsigned) ul;

        if ((unsigned long) *t != ul)
                return -1;

        return 0;
}

#define LOAD_FUNC(name)                                                 \
        do {                                                            \
                *(void**) (&real_##name) = dlsym(RTLD_NEXT, #name);     \
                assert(real_##name);                                    \
        } while (false)

#define LOAD_FUNC_VERSIONED(name, version)                              \
        do {                                                            \
                *(void**) (&real_##name) = dlvsym(RTLD_NEXT, #name, version); \
                assert(real_##name);                                    \
        } while (false)

static void load_functions(void) {
        static volatile bool loaded = false;

        if (LIKELY(loaded))
                return;

        recursive = true;

        /* If someone uses a shared library constructor that is called
         * before ours we might not be initialized yet when the first
         * lock related operation is executed. To deal with this we'll
         * simply call the original implementation and do nothing
         * else, but for that we do need the original function
         * pointers. */

        LOAD_FUNC(pthread_mutex_init);
        LOAD_FUNC(pthread_mutex_destroy);
        LOAD_FUNC(pthread_mutex_lock);
        LOAD_FUNC(pthread_mutex_trylock);
        LOAD_FUNC(pthread_mutex_timedlock);
        LOAD_FUNC(pthread_mutex_unlock);
        LOAD_FUNC(pthread_create);
        LOAD_FUNC(pthread_rwlock_init);
        LOAD_FUNC(pthread_rwlock_destroy);
        LOAD_FUNC(pthread_rwlock_rdlock);
        LOAD_FUNC(pthread_rwlock_tryrdlock);
        LOAD_FUNC(pthread_rwlock_timedrdlock);
        LOAD_FUNC(pthread_rwlock_wrlock);
        LOAD_FUNC(pthread_rwlock_trywrlock);
        LOAD_FUNC(pthread_rwlock_timedwrlock);
        LOAD_FUNC(pthread_rwlock_unlock);

        /* There's some kind of weird incompatibility problem causing
         * pthread_cond_timedwait() to freeze if we don't ask for this
         * explicit version of these functions */
        LOAD_FUNC_VERSIONED(pthread_cond_wait, "GLIBC_2.3.2");
        LOAD_FUNC_VERSIONED(pthread_cond_timedwait, "GLIBC_2.3.2");

        LOAD_FUNC(exit);
        LOAD_FUNC(_exit);
        LOAD_FUNC(_Exit);

        LOAD_FUNC(backtrace);
        LOAD_FUNC(backtrace_symbols);
        LOAD_FUNC(backtrace_symbols_fd);

        loaded = true;
        recursive = false;
}

static void setup(void) {
        pthread_mutex_t *m, *last;
        int r;
        unsigned t;

        load_functions();

        if (LIKELY(initialized))
                return;

        if (!dlsym(NULL, "main"))
                fprintf(stderr,
                        "mutrace: Application appears to be compiled without -rdynamic. It might be a\n"
                        "mutrace: good idea to recompile with -rdynamic enabled since this produces more\n"
                        "mutrace: useful stack traces.\n\n");

        if (__malloc_hook) {
                fprintf(stderr,
                        "mutrace: Detected non-glibc memory allocator. Your program uses some\n"
                        "mutrace: alternative memory allocator (jemalloc?) which is not compatible with\n"
                        "mutrace: mutrace. Please rebuild your program with the standard memory\n"
                        "mutrace: allocator or fix mutrace to handle yours correctly.\n");

                /* The reason for this is that jemalloc and other
                 * allocators tend to call pthread_mutex_xxx() from
                 * the allocator. However, we need to call malloc()
                 * ourselves from some mutex operations so this might
                 * create an endless loop eventually overflowing the
                 * stack. glibc's malloc() does locking too but uses
                 * lock routines that do not end up calling
                 * pthread_mutex_xxx(). */

                real_exit(1);
        }

        t = hash_size;
        if (parse_env("MUTRACE_HASH_SIZE", &t) < 0 || t <= 0)
                fprintf(stderr, "mutrace: WARNING: Failed to parse $MUTRACE_HASH_SIZE.\n");
        else
                hash_size = t;

        t = frames_max;
        if (parse_env("MUTRACE_FRAMES", &t) < 0 || t <= 0)
                fprintf(stderr, "mutrace: WARNING: Failed to parse $MUTRACE_FRAMES.\n");
        else
                frames_max = t;

        t = show_n_locked_min;
        if (parse_env("MUTRACE_LOCKED_MIN", &t) < 0)
                fprintf(stderr, "mutrace: WARNING: Failed to parse $MUTRACE_LOCKED_MIN.\n");
        else
                show_n_locked_min = t;

        t = show_n_owner_changed_min;
        if (parse_env("MUTRACE_OWNER_CHANGED_MIN", &t) < 0)
                fprintf(stderr, "mutrace: WARNING: Failed to parse $MUTRACE_OWNER_CHANGED_MIN.\n");
        else
                show_n_owner_changed_min = t;

        t = show_n_contended_min;
        if (parse_env("MUTRACE_CONTENDED_MIN", &t) < 0)
                fprintf(stderr, "mutrace: WARNING: Failed to parse $MUTRACE_CONTENDED_MIN.\n");
        else
                show_n_contended_min = t;

        t = show_n_max;
        if (parse_env("MUTRACE_MAX", &t) < 0)
                fprintf(stderr, "mutrace: WARNING: Failed to parse $MUTRACE_MAX.\n");
        else
                show_n_max = t;

        if (getenv("MUTRACE_TRAP"))
                raise_trap = true;

        if (getenv("MUTRACE_TRACK_RT"))
                track_rt = true;

        alive_mutexes = calloc(hash_size, sizeof(struct mutex_info*));
        assert(alive_mutexes);

        dead_mutexes = calloc(hash_size, sizeof(struct mutex_info*));
        assert(dead_mutexes);

        mutexes_lock = malloc(hash_size * sizeof(pthread_mutex_t));
        assert(mutexes_lock);

        for (m = mutexes_lock, last = mutexes_lock+hash_size; m < last; m++) {
                r = real_pthread_mutex_init(m, NULL);

                assert(r == 0);
        }

        nsec_timestamp_setup = nsec_now();

        initialized = true;

        fprintf(stderr, "mutrace: "PACKAGE_VERSION" sucessfully initialized for process %s (pid %lu).\n",
                get_prname(), (unsigned long) getpid());
}

static unsigned long mutex_hash(pthread_mutex_t *mutex) {
        unsigned long u;

        u = (unsigned long) mutex;
        u /= sizeof(void*);
        return u % hash_size;
}

static unsigned long rwlock_hash(pthread_rwlock_t *rwlock) {
        unsigned long u;

        u = (unsigned long) rwlock;
        u /= sizeof(void*);

        return u % hash_size;
}

static void lock_hash_mutex(unsigned u) {
        int r;

        r = real_pthread_mutex_trylock(mutexes_lock + u);

        if (UNLIKELY(r == EBUSY)) {
                __sync_fetch_and_add(&n_self_contended, 1);
                r = real_pthread_mutex_lock(mutexes_lock + u);
        }

        assert(r == 0);
}

static void unlock_hash_mutex(unsigned u) {
        int r;

        r = real_pthread_mutex_unlock(mutexes_lock + u);
        assert(r == 0);
}

static int mutex_info_compare(const void *_a, const void *_b) {
        const struct mutex_info
                *a = *(const struct mutex_info**) _a,
                *b = *(const struct mutex_info**) _b;

        if (a->n_contended > b->n_contended)
                return -1;
        else if (a->n_contended < b->n_contended)
                return 1;

        if (a->n_owner_changed > b->n_owner_changed)
                return -1;
        else if (a->n_owner_changed < b->n_owner_changed)
                return 1;

        if (a->n_locked > b->n_locked)
                return -1;
        else if (a->n_locked < b->n_locked)
                return 1;

        if (a->nsec_locked_max > b->nsec_locked_max)
                return -1;
        else if (a->nsec_locked_max < b->nsec_locked_max)
                return 1;

        /* Let's make the output deterministic */
        if (a > b)
                return -1;
        else if (a < b)
                return 1;

        return 0;
}

static bool mutex_info_show(struct mutex_info *mi) {

        /* Mutexes used by real-time code are always noteworthy */
        if (mi->realtime)
                return true;

        if (mi->n_locked < show_n_locked_min)
                return false;

        if (mi->n_owner_changed < show_n_owner_changed_min)
                return false;

        if (mi->n_contended < show_n_contended_min)
                return false;

        return true;
}

static bool mutex_info_dump(struct mutex_info *mi) {

        if (!mutex_info_show(mi))
                return false;

        fprintf(stderr,
                "\nMutex #%u (0x%p) first referenced by:\n"
                "%s", mi->id, mi->mutex ? (void*) mi->mutex : (void*) mi->rwlock, mi->stacktrace);

        return true;
}

static char mutex_type_name(int type) {
        switch (type) {

                case PTHREAD_MUTEX_NORMAL:
                        return '-';

                case PTHREAD_MUTEX_RECURSIVE:
                        return 'r';

                case PTHREAD_MUTEX_ERRORCHECK:
                        return 'e';

                case PTHREAD_MUTEX_ADAPTIVE_NP:
                        return 'a';

                default:
                        return '?';
        }
}

static char mutex_protocol_name(int protocol) {
        switch (protocol) {

                case PTHREAD_PRIO_NONE:
                        return '-';

                case PTHREAD_PRIO_INHERIT:
                        return 'i';

                case PTHREAD_PRIO_PROTECT:
                        return 'p';

                default:
                        return '?';
        }
}

static char rwlock_kind_name(int kind) {
        switch (kind) {

                case PTHREAD_RWLOCK_PREFER_READER_NP:
                        return 'r';

                case PTHREAD_RWLOCK_PREFER_WRITER_NP:
                        return 'w';

                case PTHREAD_RWLOCK_PREFER_WRITER_NONRECURSIVE_NP:
                        return 'W';

                default:
                        return '?';
        }
}

static bool mutex_info_stat(struct mutex_info *mi) {

        if (!mutex_info_show(mi))
                return false;

        fprintf(stderr,
                "%8u %8u %8u %8u %12.3f %12.3f %12.3f %c%c%c%c%c%c\n",
                mi->id,
                mi->n_locked,
                mi->n_owner_changed,
                mi->n_contended,
                (double) mi->nsec_locked_total / 1000000.0,
                (double) mi->nsec_locked_total / mi->n_locked / 1000000.0,
                (double) mi->nsec_locked_max / 1000000.0,
                mi->mutex ? 'M' : 'W',
                mi->broken ? '!' : (mi->dead ? 'x' : '-'),
                track_rt ? (mi->realtime ? 'R' : '-') : '.',
                mi->mutex ? mutex_type_name(mi->type) : '.',
                mi->mutex ? mutex_protocol_name(mi->protocol) : '.',
                mi->rwlock ? rwlock_kind_name(mi->kind) : '.');

        return true;
}

static void show_summary(void) {
        static pthread_mutex_t summary_mutex = PTHREAD_MUTEX_INITIALIZER;
        static bool shown_summary = false;

        struct mutex_info *mi, **table;
        unsigned n, u, i, m;
        uint64_t t;
        long n_cpus;

        real_pthread_mutex_lock(&summary_mutex);

        if (shown_summary)
                goto finish;

        t = nsec_now() - nsec_timestamp_setup;

        fprintf(stderr,
                "\n"
                "mutrace: Showing statistics for process %s (pid %lu).\n", get_prname(), (unsigned long) getpid());

        n = 0;
        for (u = 0; u < hash_size; u++) {
                lock_hash_mutex(u);

                for (mi = alive_mutexes[u]; mi; mi = mi->next)
                        n++;

                for (mi = dead_mutexes[u]; mi; mi = mi->next)
                        n++;
        }

        if (n <= 0) {
                fprintf(stderr,
                        "mutrace: No mutexes used.\n");
                goto finish;
        }

        fprintf(stderr,
                "mutrace: %u mutexes used.\n", n);

        table = malloc(sizeof(struct mutex_info*) * n);

        i = 0;
        for (u = 0; u < hash_size; u++) {
                for (mi = alive_mutexes[u]; mi; mi = mi->next) {
                        mi->id = i;
                        table[i++] = mi;
                }

                for (mi = dead_mutexes[u]; mi; mi = mi->next) {
                        mi->id = i;
                        table[i++] = mi;
                }
        }
        assert(i == n);

        qsort(table, n, sizeof(table[0]), mutex_info_compare);

        for (i = 0, m = 0; i < n && (show_n_max <= 0 || m < show_n_max); i++)
                m += mutex_info_dump(table[i]) ? 1 : 0;

        if (m > 0) {
                fprintf(stderr,
                        "\n"
                        "mutrace: Showing %u most contended mutexes:\n"
                        "\n"
                        " Mutex #   Locked  Changed    Cont. tot.Time[ms] avg.Time[ms] max.Time[ms]  Flags\n",
                        m);

                for (i = 0, m = 0; i < n && (show_n_max <= 0 || m < show_n_max); i++)
                        m += mutex_info_stat(table[i]) ? 1 : 0;


                if (i < n)
                        fprintf(stderr,
                                "     ...      ...      ...      ...          ...          ...          ... ||||||\n");
                else
                        fprintf(stderr,
                                "                                                                           ||||||\n");

                fprintf(stderr,
                        "                                                                           /|||||\n"
                        "          Object:                                     M = Mutex, W = RWLock /||||\n"
                        "           State:                                 x = dead, ! = inconsistent /|||\n"
                        "             Use:                                 R = used in realtime thread /||\n"
                        "      Mutex Type:                 r = RECURSIVE, e = ERRRORCHECK, a = ADAPTIVE /|\n"
                        "  Mutex Protocol:                                      i = INHERIT, p = PROTECT /\n"
                        "     RWLock Kind: r = PREFER_READER, w = PREFER_WRITER, W = PREFER_WRITER_NONREC \n");

                if (!track_rt)
                        fprintf(stderr,
                                "\n"
                                "mutrace: Note that the flags column R is only valid in --track-rt mode!\n");

        } else
                fprintf(stderr,
                        "\n"
                        "mutrace: No mutex contended according to filtering parameters.\n");

        free(table);

        for (u = 0; u < hash_size; u++)
                unlock_hash_mutex(u);

        fprintf(stderr,
                "\n"
                "mutrace: Total runtime is %0.3f ms.\n", (double) t / 1000000.0);

        n_cpus = sysconf(_SC_NPROCESSORS_ONLN);
        assert(n_cpus >= 1);

        if (n_cpus <= 1)
                fprintf(stderr,
                        "\n"
                        "mutrace: WARNING: Results for uniprocessor machine. Results might be more interesting\n"
                        "                  when run on an SMP machine!\n");
        else
                fprintf(stderr,
                        "\n"
                        "mutrace: Results for SMP with %li processors.\n", n_cpus);

        if (n_broken > 0)
                fprintf(stderr,
                        "\n"
                        "mutrace: WARNING: %u inconsistent mutex uses detected. Results might not be reliable.\n"
                        "mutrace:          Fix your program first!\n", n_broken);

        if (n_collisions > 0)
                fprintf(stderr,
                        "\n"
                        "mutrace: WARNING: %u internal hash collisions detected. Results might not be as reliable as they could be.\n"
                        "mutrace:          Try to increase --hash-size=, which is currently at %u.\n", n_collisions, hash_size);

        if (n_self_contended > 0)
                fprintf(stderr,
                        "\n"
                        "mutrace: WARNING: %u internal mutex contention detected. Results might not be reliable as they could be.\n"
                        "mutrace:          Try to increase --hash-size=, which is currently at %u.\n", n_self_contended, hash_size);

finish:
        shown_summary = true;

        real_pthread_mutex_unlock(&summary_mutex);
}

static void shutdown(void) {
        show_summary();
}

void exit(int status) {
        show_summary();
        real_exit(status);
}

void _exit(int status) {
        show_summary();
        real_exit(status);
}

void _Exit(int status) {
        show_summary();
        real__Exit(status);
}

static bool is_realtime(void) {
        int policy;

        policy = sched_getscheduler(_gettid());
        assert(policy >= 0);

        policy &= ~SCHED_RESET_ON_FORK;

        return
                policy == SCHED_FIFO ||
                policy == SCHED_RR;
}

static bool verify_frame(const char *s) {

        /* Generated by glibc's native backtrace_symbols() on Fedora */
        if (strstr(s, "/" SONAME "("))
                return false;

        /* Generated by glibc's native backtrace_symbols() on Debian */
        if (strstr(s, "/" SONAME " ["))
                return false;

        /* Generated by backtrace-symbols.c */
        if (strstr(s, __FILE__":"))
                return false;

        return true;
}

static char* generate_stacktrace(void) {
        void **buffer;
        char **strings, *ret, *p;
        int n, i;
        size_t k;
        bool b;

        buffer = malloc(sizeof(void*) * frames_max);
        assert(buffer);

        n = real_backtrace(buffer, frames_max);
        assert(n >= 0);

        strings = real_backtrace_symbols(buffer, n);
        assert(strings);

        free(buffer);

        k = 0;
        for (i = 0; i < n; i++)
                k += strlen(strings[i]) + 2;

        ret = malloc(k + 1);
        assert(ret);

        b = false;
        for (i = 0, p = ret; i < n; i++) {
                if (!b && !verify_frame(strings[i]))
                        continue;

                if (!b && i > 0) {
                        /* Skip all but the first stack frame of ours */
                        *(p++) = '\t';
                        strcpy(p, strings[i-1]);
                        p += strlen(strings[i-1]);
                        *(p++) = '\n';
                }

                b = true;

                *(p++) = '\t';
                strcpy(p, strings[i]);
                p += strlen(strings[i]);
                *(p++) = '\n';
        }

        *p = 0;

        free(strings);

        return ret;
}

static struct mutex_info *mutex_info_add(unsigned long u, pthread_mutex_t *mutex, int type, int protocol) {
        struct mutex_info *mi;

        /* Needs external locking */

        if (alive_mutexes[u])
                __sync_fetch_and_add(&n_collisions, 1);

        mi = calloc(1, sizeof(struct mutex_info));
        assert(mi);

        mi->mutex = mutex;
        mi->type = type;
        mi->protocol = protocol;
        mi->stacktrace = generate_stacktrace();

        mi->next = alive_mutexes[u];
        alive_mutexes[u] = mi;

        return mi;
}

static void mutex_info_remove(unsigned u, pthread_mutex_t *mutex) {
        struct mutex_info *mi, *p;

        /* Needs external locking */

        for (mi = alive_mutexes[u], p = NULL; mi; p = mi, mi = mi->next)
                if (mi->mutex == mutex)
                        break;

        if (!mi)
                return;

        if (p)
                p->next = mi->next;
        else
                alive_mutexes[u] = mi->next;

        mi->dead = true;
        mi->next = dead_mutexes[u];
        dead_mutexes[u] = mi;
}

static struct mutex_info *mutex_info_acquire(pthread_mutex_t *mutex) {
        unsigned long u;
        struct mutex_info *mi;

        u = mutex_hash(mutex);
        lock_hash_mutex(u);

        for (mi = alive_mutexes[u]; mi; mi = mi->next)
                if (mi->mutex == mutex)
                        return mi;

        /* FIXME: We assume that static mutexes are NORMAL, which
         * might not actually be correct */
        return mutex_info_add(u, mutex, PTHREAD_MUTEX_NORMAL, PTHREAD_PRIO_NONE);
}

static void mutex_info_release(pthread_mutex_t *mutex) {
        unsigned long u;

        u = mutex_hash(mutex);
        unlock_hash_mutex(u);
}

int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *mutexattr) {
        int r;
        unsigned long u;

        if (UNLIKELY(!initialized && recursive)) {
                static const pthread_mutex_t template = PTHREAD_MUTEX_INITIALIZER;
                /* Now this is incredibly ugly. */

                memcpy(mutex, &template, sizeof(pthread_mutex_t));
                return 0;
        }

        load_functions();

        r = real_pthread_mutex_init(mutex, mutexattr);
        if (r != 0)
                return r;

        if (LIKELY(initialized && !recursive)) {
                int type = PTHREAD_MUTEX_NORMAL;
                int protocol = PTHREAD_PRIO_NONE;

                recursive = true;
                u = mutex_hash(mutex);
                lock_hash_mutex(u);

                mutex_info_remove(u, mutex);

                if (mutexattr) {
                        int k;

                        k = pthread_mutexattr_gettype(mutexattr, &type);
                        assert(k == 0);

                        k = pthread_mutexattr_getprotocol(mutexattr, &protocol);
                        assert(k == 0);
                }

                mutex_info_add(u, mutex, type, protocol);

                unlock_hash_mutex(u);
                recursive = false;
        }

        return r;
}

int pthread_mutex_destroy(pthread_mutex_t *mutex) {
        unsigned long u;

        assert(initialized || !recursive);

        load_functions();

        if (LIKELY(initialized && !recursive)) {
                recursive = true;

                u = mutex_hash(mutex);
                lock_hash_mutex(u);

                mutex_info_remove(u, mutex);

                unlock_hash_mutex(u);

                recursive = false;
        }

        return real_pthread_mutex_destroy(mutex);
}

static void mutex_lock(pthread_mutex_t *mutex, bool busy) {
        struct mutex_info *mi;
        pid_t tid;

        if (UNLIKELY(!initialized || recursive))
                return;

        recursive = true;
        mi = mutex_info_acquire(mutex);

        if (mi->n_lock_level > 0 && mi->type != PTHREAD_MUTEX_RECURSIVE) {
                __sync_fetch_and_add(&n_broken, 1);
                mi->broken = true;

                if (raise_trap)
                        DEBUG_TRAP;
        }

        mi->n_lock_level++;
        mi->n_locked++;

        if (busy)
                mi->n_contended++;

        tid = _gettid();
        if (mi->last_owner != tid) {
                if (mi->last_owner != 0)
                        mi->n_owner_changed++;

                mi->last_owner = tid;
        }

        if (track_rt && !mi->realtime && is_realtime())
                mi->realtime = true;

        mi->nsec_timestamp = nsec_now();

        mutex_info_release(mutex);
        recursive = false;
}

int pthread_mutex_lock(pthread_mutex_t *mutex) {
        int r;
        bool busy;

        if (UNLIKELY(!initialized && recursive)) {
                /* During the initialization phase we might be called
                 * inside of dlsym(). Since we'd enter an endless loop
                 * if we tried to resolved the real
                 * pthread_mutex_lock() here then we simply fake the
                 * lock which should be safe since no thread can be
                 * running yet. */

                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_mutex_trylock(mutex);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        if (UNLIKELY((busy = (r == EBUSY)))) {
                r = real_pthread_mutex_lock(mutex);

                if (UNLIKELY(r != 0))
                        return r;
        }

        mutex_lock(mutex, busy);
        return r;
}

int pthread_mutex_timedlock(pthread_mutex_t *mutex, const struct timespec *abstime) {
        int r;
        bool busy;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_mutex_trylock(mutex);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        if (UNLIKELY((busy = (r == EBUSY)))) {
                r = real_pthread_mutex_timedlock(mutex, abstime);

                if (UNLIKELY(r == ETIMEDOUT))
                        busy = true;
                else if (UNLIKELY(r != 0))
                        return r;
        }

        mutex_lock(mutex, busy);
        return r;
}

int pthread_mutex_trylock(pthread_mutex_t *mutex) {
        int r;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_mutex_trylock(mutex);
        if (UNLIKELY(r != 0))
                return r;

        mutex_lock(mutex, false);
        return r;
}

static void mutex_unlock(pthread_mutex_t *mutex) {
        struct mutex_info *mi;
        uint64_t t;

        if (UNLIKELY(!initialized || recursive))
                return;

        recursive = true;
        mi = mutex_info_acquire(mutex);

        if (mi->n_lock_level <= 0) {
                __sync_fetch_and_add(&n_broken, 1);
                mi->broken = true;

                if (raise_trap)
                        DEBUG_TRAP;
        }

        mi->n_lock_level--;

        t = nsec_now() - mi->nsec_timestamp;
        mi->nsec_locked_total += t;

        if (t > mi->nsec_locked_max)
                mi->nsec_locked_max = t;

        mutex_info_release(mutex);
        recursive = false;
}

int pthread_mutex_unlock(pthread_mutex_t *mutex) {

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        mutex_unlock(mutex);

        return real_pthread_mutex_unlock(mutex);
}

int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex) {
        int r;

        assert(initialized || !recursive);

        load_functions();

        mutex_unlock(mutex);
        r = real_pthread_cond_wait(cond, mutex);

        /* Unfortunately we cannot distuingish mutex contention and
         * the condition not being signalled here. */
        mutex_lock(mutex, false);

        return r;
}

int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t *mutex, const struct timespec *abstime) {
        int r;

        assert(initialized || !recursive);

        load_functions();

        mutex_unlock(mutex);
        r = real_pthread_cond_timedwait(cond, mutex, abstime);
        mutex_lock(mutex, false);

        return r;
}

int pthread_create(pthread_t *newthread,
                   const pthread_attr_t *attr,
                   void *(*start_routine) (void *),
                   void *arg) {

        load_functions();

        if (UNLIKELY(!threads_existing)) {
                threads_existing = true;
                setup();
        }

        return real_pthread_create(newthread, attr, start_routine, arg);
}

int backtrace(void **array, int size) {
        int r;

        load_functions();

        /* backtrace() internally uses a mutex. To avoid an endless
         * loop we need to disable ourselves so that we don't try to
         * call backtrace() ourselves when looking at that lock. */

        recursive = true;
        r = real_backtrace(array, size);
        recursive = false;

        return r;
}

char **backtrace_symbols(void *const *array, int size) {
        char **r;

        load_functions();

        recursive = true;
        r = real_backtrace_symbols(array, size);
        recursive = false;

        return r;
}

void backtrace_symbols_fd(void *const *array, int size, int fd) {
        load_functions();

        recursive = true;
        real_backtrace_symbols_fd(array, size, fd);
        recursive = false;
}

static struct mutex_info *rwlock_info_add(unsigned long u, pthread_rwlock_t *rwlock, int kind) {
        struct mutex_info *mi;

        /* Needs external locking */

        if (alive_mutexes[u])
                __sync_fetch_and_add(&n_collisions, 1);

        mi = calloc(1, sizeof(struct mutex_info));
        assert(mi);

        mi->rwlock = rwlock;
        mi->kind = kind;
        mi->stacktrace = generate_stacktrace();

        mi->next = alive_mutexes[u];
        alive_mutexes[u] = mi;

        return mi;
}

static void rwlock_info_remove(unsigned u, pthread_rwlock_t *rwlock) {
        struct mutex_info *mi, *p;

        /* Needs external locking */

        for (mi = alive_mutexes[u], p = NULL; mi; p = mi, mi = mi->next)
                if (mi->rwlock == rwlock)
                        break;

        if (!mi)
                return;

        if (p)
                p->next = mi->next;
        else
                alive_mutexes[u] = mi->next;

        mi->dead = true;
        mi->next = dead_mutexes[u];
        dead_mutexes[u] = mi;
}

static struct mutex_info *rwlock_info_acquire(pthread_rwlock_t *rwlock) {
        unsigned long u;
        struct mutex_info *mi;

        u = rwlock_hash(rwlock);
        lock_hash_mutex(u);

        for (mi = alive_mutexes[u]; mi; mi = mi->next)
                if (mi->rwlock == rwlock)
                        return mi;

        /* FIXME: We assume that static mutexes are RWLOCK_DEFAULT,
         * which might not actually be correct */
        return rwlock_info_add(u, rwlock, PTHREAD_RWLOCK_DEFAULT_NP);
}

static void rwlock_info_release(pthread_rwlock_t *rwlock) {
        unsigned long u;

        u = rwlock_hash(rwlock);
        unlock_hash_mutex(u);
}

int pthread_rwlock_init(pthread_rwlock_t *rwlock, const pthread_rwlockattr_t *attr) {
        int r;
        unsigned long u;

        if (UNLIKELY(!initialized && recursive)) {
                static const pthread_rwlock_t template = PTHREAD_RWLOCK_INITIALIZER;
                /* Now this is incredibly ugly. */

                memcpy(rwlock, &template, sizeof(pthread_rwlock_t));
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_init(rwlock, attr);
        if (r != 0)
                return r;

        if (LIKELY(initialized && !recursive)) {
                int kind = PTHREAD_RWLOCK_DEFAULT_NP;

                recursive = true;
                u = rwlock_hash(rwlock);
                lock_hash_mutex(u);

                rwlock_info_remove(u, rwlock);

                if (attr) {
                        int k;

                        k = pthread_rwlockattr_getkind_np(attr, &kind);
                        assert(k == 0);
                }

                rwlock_info_add(u, rwlock, kind);

                unlock_hash_mutex(u);
                recursive = false;
        }

        return r;
}

int pthread_rwlock_destroy(pthread_rwlock_t *rwlock) {
        unsigned long u;

        assert(initialized || !recursive);

        load_functions();

        if (LIKELY(initialized && !recursive)) {
                recursive = true;

                u = rwlock_hash(rwlock);
                lock_hash_mutex(u);

                rwlock_info_remove(u, rwlock);

                unlock_hash_mutex(u);

                recursive = false;
        }

        return real_pthread_rwlock_destroy(rwlock);
}

static void rwlock_lock(pthread_rwlock_t *rwlock, bool for_write, bool busy) {
        struct mutex_info *mi;
        pid_t tid;

        if (UNLIKELY(!initialized || recursive))
                return;

        recursive = true;
        mi = rwlock_info_acquire(rwlock);

        if (mi->n_lock_level > 0 && for_write) {
                __sync_fetch_and_add(&n_broken, 1);
                mi->broken = true;

                if (raise_trap)
                        DEBUG_TRAP;
        }

        mi->n_lock_level++;
        mi->n_locked++;

        if (busy)
                mi->n_contended++;

        tid = _gettid();
        if (mi->last_owner != tid) {
                if (mi->last_owner != 0)
                        mi->n_owner_changed++;

                mi->last_owner = tid;
        }

        if (track_rt && !mi->realtime && is_realtime())
                mi->realtime = true;

        mi->nsec_timestamp = nsec_now();

        rwlock_info_release(rwlock);
        recursive = false;
}

int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock) {
        int r;
        bool busy;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_tryrdlock(rwlock);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        if (UNLIKELY((busy = (r == EBUSY)))) {
                r = real_pthread_rwlock_rdlock(rwlock);

                if (UNLIKELY(r == ETIMEDOUT))
                        busy = true;
                else if (UNLIKELY(r != 0))
                        return r;
        }

        rwlock_lock(rwlock, false, busy);
        return r;
}

int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock) {
        int r;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_tryrdlock(rwlock);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        rwlock_lock(rwlock, false, false);
        return r;
}

int pthread_rwlock_timedrdlock(pthread_rwlock_t *rwlock, const struct timespec *abstime) {
        int r;
        bool busy;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_tryrdlock(rwlock);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        if (UNLIKELY((busy = (r == EBUSY)))) {
                r = real_pthread_rwlock_timedrdlock(rwlock, abstime);

                if (UNLIKELY(r == ETIMEDOUT))
                        busy = true;
                else if (UNLIKELY(r != 0))
                        return r;
        }

        rwlock_lock(rwlock, false, busy);
        return r;
}

int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock) {
        int r;
        bool busy;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_trywrlock(rwlock);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        if (UNLIKELY((busy = (r == EBUSY)))) {
                r = real_pthread_rwlock_wrlock(rwlock);

                if (UNLIKELY(r == ETIMEDOUT))
                        busy = true;
                else if (UNLIKELY(r != 0))
                        return r;
        }

        rwlock_lock(rwlock, true, busy);
        return r;
}

int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock) {
        int r;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_trywrlock(rwlock);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        rwlock_lock(rwlock, true, false);
        return r;
}

int pthread_rwlock_timedwrlock(pthread_rwlock_t *rwlock, const struct timespec *abstime) {
        int r;
        bool busy;

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        r = real_pthread_rwlock_trywrlock(rwlock);
        if (UNLIKELY(r != EBUSY && r != 0))
                return r;

        if (UNLIKELY((busy = (r == EBUSY)))) {
                r = real_pthread_rwlock_timedwrlock(rwlock, abstime);

                if (UNLIKELY(r == ETIMEDOUT))
                        busy = true;
                else if (UNLIKELY(r != 0))
                        return r;
        }

        rwlock_lock(rwlock, true, busy);
        return r;
}

static void rwlock_unlock(pthread_rwlock_t *rwlock) {
        struct mutex_info *mi;
        uint64_t t;

        if (UNLIKELY(!initialized || recursive))
                return;

        recursive = true;
        mi = rwlock_info_acquire(rwlock);

        if (mi->n_lock_level <= 0) {
                __sync_fetch_and_add(&n_broken, 1);
                mi->broken = true;

                if (raise_trap)
                        DEBUG_TRAP;
        }

        mi->n_lock_level--;

        t = nsec_now() - mi->nsec_timestamp;
        mi->nsec_locked_total += t;

        if (t > mi->nsec_locked_max)
                mi->nsec_locked_max = t;

        rwlock_info_release(rwlock);
        recursive = false;
}

int pthread_rwlock_unlock(pthread_rwlock_t *rwlock) {

        if (UNLIKELY(!initialized && recursive)) {
                assert(!threads_existing);
                return 0;
        }

        load_functions();

        rwlock_unlock(rwlock);

        return real_pthread_rwlock_unlock(rwlock);
}
