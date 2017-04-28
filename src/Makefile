all: libz0.so z0.so
	mkdir -p ../lib
	mv z0.so ../lib/z0.so
	mv libz0.so ../lib/libz0.so

CXXFLAGS = -rdynamic $(shell llvm-config --cxxflags) -ggdb -I/home/user/z3-4.5.0-x64-debian-8.5/include -fexceptions -lz3 -fdiagnostics-color -O1
CFLAGS = -fPIC -Wall -Wextra

%.so: %.o
	$(CXX) -dylib -shared $^ -o $@
clean:
	rm -f *.o *~ *.so *.bc
