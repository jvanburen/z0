all: z0.so

Z3SO=../../

CXXFLAGS = -rdynamic $(shell llvm-config --cxxflags) -g -O0 -I/home/user/z3-4.5.0-x64-debian-8.5/include -fexceptions -lz3

%.so: %.o
	$(CXX) -dylib -shared $^ -o $@
clean:
	rm -f *.o *~ *.so *.bc
