/* EXPECT on=2 off=2 */
/* A static declaration without definition. */
static double floor(double x);
double f(double x) { return floor(x) + floor(x); }
