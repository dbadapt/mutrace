SONAME=libmutrace.so
CFLAGS=-Wextra -Wall -O0 -g -DPACKAGE_VERSION=\"0.1\" -fPIC -DSONAME=\"$(SONAME)\"
LIBS=-lrt -ldl

$(SONAME): mutrace.o
	$(CC) $(CFLAGS) $(LIBS) -shared -o $@ $^

clean:
	-rm -f *.o libmutrace.so
