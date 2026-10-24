/* EXPECT on=4 off=4 */
/* Not the C99 prototypes: an extra argument, a missing argument. */
double floor(double, double);
double pow(double);
double f(double x) { return floor(x, x) + floor(x, x) + pow(x) + pow(x); }
