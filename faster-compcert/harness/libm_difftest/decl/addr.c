/* EXPECT on=1 off=2 */
/* The address is taken: direct calls are still shared, and the indirect
   calls (not counted) remain. */
#include <math.h>
double (*p)(double) = floor;
double f(double x) { return floor(x) + floor(x) + p(x) + p(x); }
