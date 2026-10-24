/* EXPECT on=0 off=1 */
/* The result is unused: the call is removed. */
#include <math.h>
void f(double x) { floor(x); }
