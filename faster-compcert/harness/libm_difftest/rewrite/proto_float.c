/* EXPECT sqrt=call fabs=call */
/* Not the C99 prototype: float instead of double. */
float sqrt(float);
float fabs(float);
float f(float x) { return sqrt(x) + fabs(x) + 1.0f; }
