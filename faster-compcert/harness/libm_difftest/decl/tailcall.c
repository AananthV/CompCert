/* EXPECT on=2 off=2 */
/* The second call is in tail position: it becomes a tail call before CSE,
   and CSE does not share tail calls (a limitation, not an error). */
#include <math.h>
double f(double x) { double a = floor(x); if (a > 0) return floor(x); return a; }
