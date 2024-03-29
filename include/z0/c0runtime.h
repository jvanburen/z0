/* This defines C functions and types that CC0-generated code uses */
/* Significant portions copied from cc0lib.h and c0runtime.h */

/* C0 Runtime Interface
 * Shared between the libraries and the runtime
 *
 * Individual runtimes may inline individual operations with #define
 * (the unsafe runtime does this for most operations, actually), but
 * the runtime must still provide all implementations for the benefit
 * of library functions that may want to use them.
 *
 * Frank Pfenning, Rob Arnold, William Lovas, Rob Simmons
 */

#ifndef __C0RUNTIME_H__
#define __C0RUNTIME_H__

#include <stdlib.h>
#include <stdbool.h>

/* C0 types */

typedef int c0_int;
typedef bool c0_bool;
typedef char c0_char;
typedef const char* c0_string;                  // NULL is the empty string
typedef struct c0_array_header* c0_array; // NULL is a 0-element array
typedef void* c0_pointer;                 // NULL is a null pointer
typedef struct c0_tagged_struct* c0_tagged_ptr;

/* Initialization and control */

// Called before program
void c0_runtime_init();

// Called after the program exits normally
void c0_runtime_cleanup();

// Abnormal termination: abort execution and notify the user of the reason
void c0_error(const char *msg);    // error(msg)
void c0_abort(const char *reason); // assert(false)


/* Primitive arithmetic operations - may raise SIGFPE */

c0_int c0_idiv(c0_int x, c0_int y); // x/y
c0_int c0_imod(c0_int x, c0_int y); // x%y
c0_int c0_sal(c0_int x, c0_int y);  // x<<y
c0_int c0_sar(c0_int x, c0_int y);  // x>>y


/* Allocation and dereference - may raise SIGSEGV */

// Allocate from the GC heap
c0_pointer c0_alloc(size_t bytes);

// Dereference a pointer (check for NULL in a safe runtime)
void* c0_deref(c0_pointer a);

// Allocate an array of (elemcount) elements with (elemsize) bytes per element
c0_array c0_array_alloc(size_t elemsize, c0_int elemcount);

// Returns a pointer to the element at the given index of the given array
// Runtimes may ignore the element size
void* c0_array_sub(c0_array a, int idx, size_t elemsize);

#ifdef C0_RUNTIME_IMPLEMENTS_LENGTH
// Returns the length of the array. This is only permitted in certain C0
// programs since not all runtimes may support it.
c0_int c0_array_length(c0_array a);
#endif

/* Tagged values of type C1 type void* */
c0_tagged_ptr c0_tag_ptr(char* tyrep, c0_pointer a);
void* c0_untag_ptr(char* tyrep, c0_tagged_ptr p);
c0_bool c0_tagged_eq(c0_tagged_ptr p, c0_tagged_ptr q);
c0_bool c0_hastag(char* tyrep, c0_tagged_ptr q);

/* Primitive operations on characters and strings */

bool c0_char_equal(c0_char a, c0_char b);
int c0_char_compare(c0_char a, c0_char b);

c0_string c0_string_empty();
c0_int c0_string_length(c0_string s);
bool c0_string_equal(c0_string a, c0_string b);
int c0_string_compare(c0_string a, c0_string b);

// String subscript
// Requires that i be less than the length of the string, aborts otherwise
c0_char c0_string_charat(c0_string s, int i);

// Substring
// Requires 0 <= start && start <= end && end <= \length(s)
c0_string c0_string_sub(c0_string s, int start, int end);

// Concatenation
c0_string c0_string_join(c0_string a, c0_string b);

// Construct an internal string from a null-terminated string
// Assumes that the argument may be later modified or freed
// c0_string c0_string_fromcstr(const char *s);
#define c0_string_fromcstr(s) s

// Construct an internal string from a null-terminated string
// Assumes that the argument will *never* be modified or freed
// c0_string c0_string_fromliteral(const char *s);
#define c0_string_fromliteral(s) s

// Construct a null-terminated string from an internal string,
// possibly allocating outside of the GC. The string that is returned
// must be explicitly deallocated by calling c0_string_freecstr.
const char *c0_string_tocstr(c0_string s);
void c0_string_freecstr(const char *s);

// Interpreter FFI
enum c0_val_kind { C0_INTEGER, C0_POINTER };

typedef struct c0_value {
  enum c0_val_kind kind;
  union {
    c0_int i;
    void *p;
  } payload;
} c0_value;

static inline c0_value int2val(c0_int i) {
  c0_value v;
  v.kind = C0_INTEGER;
  v.payload.i = i;
  return v;
}

static inline c0_int val2int(c0_value v) {
  if (v.kind != C0_INTEGER )
    c0_abort("Invalid cast from a c0_value (a pointer) to an integer");
  return v.payload.i;
}

static inline c0_value ptr2val(c0_pointer p) {
  c0_value v;
  v.kind = C0_POINTER;
  v.payload.p = p;
  return v;
}

static inline c0_pointer val2ptr(c0_value v) {
  if (v.kind != C0_POINTER)
    c0_abort("Invalid cast from a c0_value (an integer) to a pointer");
  return v.payload.p;
}

#endif // __C0RUNTIME_H__
