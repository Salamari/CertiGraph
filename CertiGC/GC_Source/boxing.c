#include "boxing.h"

/* The following 5 functions should (in practice) compile correctly in CompCert,
   but the CompCert correctness specification does not _require_ that
   they compile correctly:  their semantics is "undefined behavior" in
   CompCert C (and in C11), but in practice they will work in any compiler. */

int test_int_or_ptr (value x) /* returns 1 if int, 0 if aligned ptr */ {
    return (int)(((intnat)x)&1);
}

intnat int_or_ptr_to_int (value x) /* precondition: is int */ {
    return (intnat)x;
}

void * int_or_ptr_to_ptr (value x) /* precond: is aligned ptr */ {
    return (void *)x;
}

value int_to_int_or_ptr(intnat x) /* precondition: is odd */ {
    return (value)x;
}

value ptr_to_int_or_ptr(void *x) /* precondition: is aligned */ {
    return (value)x;
}
