/* EXPECT sqrt=call fabs=call */
/* OPTIONS -fno-inline */
/* The program defines its own sqrt and fabs. */
double sqrt(double x) { return x * 0.5; }
double fabs(double x) { return x; }
double f(double x) { return sqrt(x) + fabs(x) + 1.0; }
