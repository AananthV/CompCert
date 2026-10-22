/* Run the instructions of hw.s on test vectors and print, for each test,
   "<instr> <register operand> <memory operand> <result>" in hexadecimal.
   Usage: hw [number of random tests per instruction] [seed] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

double hw_addsd(const double *, double), hw_subsd(const double *, double),
       hw_mulsd(const double *, double), hw_divsd(const double *, double);
int hw_addl(const int *, int), hw_xorl(const int *, int),
    hw_andl(const int *, int), hw_orl(const int *, int);

static uint64_t state;
static uint64_t rnd(void) {          /* xorshift64* */
  state ^= state >> 12; state ^= state << 25; state ^= state >> 27;
  return state * 2685821657736338717ULL;
}

/* Special doubles: zeros, infinities, quiet and signaling NaNs with
   various payloads and signs, denormals, normal extremes. */
static const uint64_t special_d[] = {
  0x0000000000000000ULL, 0x8000000000000000ULL,   /* +0, -0 */
  0x7ff0000000000000ULL, 0xfff0000000000000ULL,   /* +inf, -inf */
  0x7ff8000000000000ULL, 0xfff8000000000000ULL,   /* default qNaNs */
  0x7ff8000000000001ULL, 0xfffc00000000abcdULL,   /* qNaNs with payload */
  0x7ff0000000000001ULL, 0xfff4000000001234ULL,   /* sNaNs */
  0x0000000000000001ULL, 0x8000000000000001ULL,   /* smallest denormals */
  0x000fffffffffffffULL, 0x800fffffffffffffULL,   /* largest denormals */
  0x0010000000000000ULL, 0x7fefffffffffffffULL,   /* min normal, max */
  0xffefffffffffffffULL, 0x3ff0000000000000ULL,   /* -max, 1 */
  0xbff0000000000000ULL, 0x3fb999999999999aULL,   /* -1, 0.1 */
  0x4000000000000000ULL, 0x3ca0000000000000ULL,   /* 2, 2^-53 */
  0x7fe0000000000000ULL, 0x0008000000000000ULL,   /* 2^1023, denormal */
};
static const uint32_t special_i[] = {
  0, 1, 0xffffffffu, 0x80000000u, 0x7fffffffu, 2, 0x55555555u, 0xaaaaaaaau,
  0x0000ffffu, 0xffff0000u,
};
#define NSD (sizeof(special_d) / sizeof(special_d[0]))
#define NSI (sizeof(special_i) / sizeof(special_i[0]))

static uint64_t dbits(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static double dval(uint64_t u) { double d; memcpy(&d, &u, 8); return d; }

static void test_d(const char *name, double (*f)(const double *, double),
                   uint64_t x, uint64_t m) {
  double mem = dval(m);
  printf("%s %016llx %016llx %016llx\n", name, (unsigned long long) x,
         (unsigned long long) m, (unsigned long long) dbits(f(&mem, dval(x))));
}

static void test_i(const char *name, int (*f)(const int *, int),
                   uint32_t x, uint32_t m) {
  int mem = (int) m;
  printf("%s %08x %08x %08x\n", name, x, m, (uint32_t) f(&mem, (int) x));
}

static uint64_t random_double(void) {
  /* Mix uniformly random bit patterns and "ordinary" doubles. */
  switch (rnd() % 4) {
  case 0: return rnd();
  case 1: return special_d[rnd() % NSD] ^ (rnd() & 0xf);
  default: { double d = ((double) (int64_t) rnd()) / (double) (1 + (rnd() % 1000000));
             return dbits(d); }
  }
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 20000;
  state = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x9e3779b97f4a7c15ULL;
  struct { const char *name; double (*f)(const double *, double); } dops[] = {
    {"addsd", hw_addsd}, {"subsd", hw_subsd}, {"mulsd", hw_mulsd}, {"divsd", hw_divsd} };
  struct { const char *name; int (*f)(const int *, int); } iops[] = {
    {"addl", hw_addl}, {"xorl", hw_xorl}, {"andl", hw_andl}, {"orl", hw_orl} };
  for (int k = 0; k < 4; k++) {
    for (unsigned i = 0; i < NSD; i++)
      for (unsigned j = 0; j < NSD; j++)
        test_d(dops[k].name, dops[k].f, special_d[i], special_d[j]);
    for (int i = 0; i < n; i++)
      test_d(dops[k].name, dops[k].f, random_double(), random_double());
    for (unsigned i = 0; i < NSI; i++)
      for (unsigned j = 0; j < NSI; j++)
        test_i(iops[k].name, iops[k].f, special_i[i], special_i[j]);
    for (int i = 0; i < n; i++) {
      uint32_t x = rnd() % 3 ? (uint32_t) rnd() : special_i[rnd() % NSI];
      uint32_t m = rnd() % 3 ? (uint32_t) rnd() : special_i[rnd() % NSI];
      test_i(iops[k].name, iops[k].f, x, m);
    }
  }
  return 0;
}
