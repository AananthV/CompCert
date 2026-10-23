/* EXPECT sqrt=call fabs=builtin */
/* The address of sqrt is taken (but not that of fabs). */
#include <math.h>
double (*p)(double);
double f(double x) { p = &sqrt; return sqrt(x) + fabs(x) + 1.0; }
