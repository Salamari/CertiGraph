#include "config.h"
#include "values.h"

extern int test_int_or_ptr (value x); /* returns 1 if int, 0 if aligned ptr */
extern intnat int_or_ptr_to_int (value x); /* precondition: is int */
extern void * int_or_ptr_to_ptr (value x); /* precond: is aligned ptr */
extern value int_to_int_or_ptr(intnat x); /* precondition: is odd */
extern value ptr_to_int_or_ptr(void *x); /* precondition: is aligned */
