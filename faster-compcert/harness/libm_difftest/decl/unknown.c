/* EXPECT on=2 off=2 */
/* A call to an unknown function between the two calls: CSE forgets
   everything (not a correctness issue, a limitation of CSE). */
#include <math.h>
extern void h(void);
double f(double x) { double a = floor(x); h(); return a + floor(x); }
