/* EXPECT sqrt=builtin fabs=builtin */
/* Block-scope declarations, and a typedef for double. */
typedef double real;
real f(real x) {
  extern real sqrt(real);
  extern double fabs(double);
  return sqrt(x) + fabs(x) + 1.0;
}
