/* EXPECT on=2 off=2 */
/* OPTIONS -fno-inline */
/* A static floor. */
static double floor(double x) { return x - 1; }
double f(double x) { return floor(x) + floor(x); }
