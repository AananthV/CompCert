/* EXPECT sqrt=call fabs=builtin */
/* OPTIONS -fno-inline */
/* A static sqrt is not the C library's. */
static double sqrt(double x);
double fabs(double x);
double f(double x) { return sqrt(x) + fabs(x) + 1.0; }
static double sqrt(double x) { return x * 0.5; }
