/* EXPECT on=2 off=2 */
/* OPTIONS -fno-inline */
/* The program defines its own floor. */
double floor(double x);
double f(double x) { return floor(x) + floor(x); }
double floor(double x) { return x - 1; }
