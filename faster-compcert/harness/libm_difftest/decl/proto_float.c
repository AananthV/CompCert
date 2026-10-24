/* EXPECT on=4 off=4 */
/* Not the C99 prototypes: float floor(float), double floorf(double). */
float floor(float);
double floorf(double);
double f(float x, double y) { return floor(x) + floor(x) + floorf(y) + floorf(y); }
