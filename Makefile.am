# This file is part of mutrace.
#
# Copyright 2009 Lennart Poettering
#
# mutrace is free software: you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# mutrace is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with mutrace. If not, see <http://www.gnu.org/licenses/>.

EXTRA_DIST = \
	bootstrap.sh \
	LGPL \
	README \
	mutrace.in

#include_HEADERS = \
#	mutrace.h

lib_LTLIBRARIES = \
	libmutrace.la

bin_SCRIPTS = \
	mutrace

CLEANFILES = \
	mutrace

libmutrace_la_SOURCES = \
	mutrace.c
libmutrace_la_LDFLAGS = \
	-avoid-version \
	-module \
	-export-dynamic \
	-shared \
	-prefer-pic
libmutrace_la_LIBADD = \
	$(PTHREAD_LIBS) \
	-lrt \
	-ldl
libmutrace_la_CFLAGS = \
	$(PTHREAD_CFLAGS) \
	-DSONAME=\"libmutrace.so\"

mutrace: mutrace.in Makefile
	sed -e 's,@PACKAGE_STRING\@,$(PACKAGE_STRING),g' \
                -e 's,@PACKAGE_NAME\@,$(PACKAGE_NAME),g' < $< > $@
	chmod +x mutrace

install-exec-hook:
	rm -f $(DESTDIR)$(libdir)/libmutrace.la

ACLOCAL_AMFLAGS = -I m4
