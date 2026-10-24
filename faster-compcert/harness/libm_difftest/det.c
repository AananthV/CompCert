/* Purity of the C library functions that -ftrust-libm treats as pure
   (issue #12, phase 2; the list is libm_*_names in common/Builtins0.v).
   For each function and input:
   - pass 1 calls the function twice in a row; the two results must have
     the same bits and set the same errno;
   - pass 2 calls the functions again on the same inputs, in a random
     order across functions and inputs; the results and errno must be those
     of pass 1 (no hidden state);
   - a memory canary must be unchanged at the end.
   It prints one line per function ("fn NAME calls N errno_set E hash H",
   where H is a hash of all the results of pass 1) and a summary line, and
   exits 1 on any mismatch.  pure.sh checks that nothing else is printed.
   Usage: det [number of random inputs per function] [seed]
   Compile with -fno-builtin: the functions are called through volatile
   pointers, so that the compiler cannot evaluate or inline them. */
#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef double (*d1)(double);
typedef double (*d2)(double, double);
typedef float (*s1)(float);
typedef float (*s2)(float, float);

struct fn { const char *name; void (*volatile p)(void); int arity, single; };
#define F(f, a, s) { #f, (void (*)(void)) f, a, s }
static struct fn fns[] = {
  F(floor,1,0), F(ceil,1,0), F(trunc,1,0), F(round,1,0),
  F(sin,1,0), F(cos,1,0), F(tan,1,0), F(asin,1,0), F(acos,1,0), F(atan,1,0),
  F(sinh,1,0), F(cosh,1,0), F(tanh,1,0),
  F(exp,1,0), F(exp2,1,0), F(expm1,1,0), F(log,1,0), F(log2,1,0), F(log10,1,0),
  F(log1p,1,0), F(cbrt,1,0),
  F(pow,2,0), F(atan2,2,0), F(fmod,2,0), F(hypot,2,0),
  F(floorf,1,1), F(ceilf,1,1), F(truncf,1,1), F(roundf,1,1),
  F(sinf,1,1), F(cosf,1,1), F(tanf,1,1), F(asinf,1,1), F(acosf,1,1), F(atanf,1,1),
  F(sinhf,1,1), F(coshf,1,1), F(tanhf,1,1),
  F(expf,1,1), F(exp2f,1,1), F(expm1f,1,1), F(logf,1,1), F(log2f,1,1), F(log10f,1,1),
  F(log1pf,1,1), F(cbrtf,1,1),
  F(powf,2,1), F(atan2f,2,1), F(fmodf,2,1), F(hypotf,2,1),
};
#define NF (sizeof fns / sizeof fns[0])

static uint64_t state;
static uint64_t rnd(void) {          /* xorshift64* */
  state ^= state >> 12; state ^= state << 25; state ^= state >> 27;
  return state * 2685821657736338717ULL;
}

/* Special values: zeros, infinities, quiet and signalling NaNs with
   payloads and both signs, subnormals, normal extremes, +-1, +-0.5,
   overflow and underflow thresholds of exp, pi, 2^52 (2^23). */
static const uint64_t sp64[] = {
  0x0000000000000000ULL, 0x8000000000000000ULL, 0x7ff0000000000000ULL,
  0xfff0000000000000ULL, 0x7ff8000000000000ULL, 0xfff8000000000001ULL,
  0x7ffc00000000abcdULL, 0x7ff4000000001234ULL, 0xfff0000000000001ULL,
  0x0000000000000001ULL, 0x800fffffffffffffULL, 0x0010000000000000ULL,
  0x7fefffffffffffffULL, 0xffefffffffffffffULL, 0x3ff0000000000000ULL,
  0xbff0000000000000ULL, 0x3fe0000000000000ULL, 0xbfe0000000000000ULL,
  0x40862e42fefa39efULL, 0x40862e42fefa39f0ULL, 0xc0874910d52d3051ULL,
  0xc0874910d52d3052ULL, 0x400921fb54442d18ULL, 0x4330000000000000ULL,
  0x4090000000000000ULL, 0xc090000000000000ULL,
};
static const uint32_t sp32[] = {
  0x00000000u, 0x80000000u, 0x7f800000u, 0xff800000u, 0x7fc00000u,
  0xffc00001u, 0x7fe0abcdu, 0x7fa00123u, 0xff800001u, 0x00000001u,
  0x807fffffu, 0x00800000u, 0x7f7fffffu, 0xff7fffffu, 0x3f800000u,
  0xbf800000u, 0x3f000000u, 0xbf000000u, 0x42b17217u, 0x42b17218u,
  0xc2cff1b4u, 0xc2cff1b5u, 0x40490fdbu, 0x4b000000u, 0x43000000u,
  0xc3000000u,
};
#define NSP (sizeof sp64 / sizeof sp64[0])

static unsigned char canary[1 << 16];

static uint64_t call(const struct fn *f, uint64_t a, uint64_t b, int *err) {
  uint64_t r;
  errno = 0;
  if (!f->single) {
    double x, y, z;
    memcpy(&x, &a, 8); memcpy(&y, &b, 8);
    z = f->arity == 1 ? ((d1) f->p)(x) : ((d2) f->p)(x, y);
    memcpy(&r, &z, 8);
  } else {
    float x, y, z; uint32_t a32 = (uint32_t) a, b32 = (uint32_t) b, r32;
    memcpy(&x, &a32, 4); memcpy(&y, &b32, 4);
    z = f->arity == 1 ? ((s1) f->p)(x) : ((s2) f->p)(x, y);
    memcpy(&r32, &z, 4); r = r32;
  }
  *err = errno;
  return r;
}

/* Input i of function f: the special values (all pairs for binary
   functions), then random bit patterns. */
static long nspecial(const struct fn *f) { return f->arity == 1 ? NSP : NSP * NSP; }
static uint64_t *RA, *RB;
static void input(const struct fn *f, long i, uint64_t *a, uint64_t *b) {
  long ns = nspecial(f);
  if (i < ns) {
    long j = f->arity == 1 ? i : i / NSP, k = f->arity == 1 ? 0 : i % NSP;
    *a = f->single ? sp32[j] : sp64[j];
    *b = f->single ? sp32[k] : sp64[k];
  } else {
    *a = RA[i - ns]; *b = RB[i - ns];
    if (f->single) { *a &= 0xffffffffu; *b &= 0xffffffffu; }
  }
}

int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 100000;
  state = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x9e3779b97f4a7c15ULL;
  if (state == 0) state = 1;
  long maxin = n + (long) (NSP * NSP);
  RA = malloc(n * 8); RB = malloc(n * 8);
  uint64_t *R[NF]; int *E[NF]; long cnt[NF];
  for (long i = 0; i < n; i++) { RA[i] = rnd(); RB[i] = rnd(); }
  memset(canary, 0x5a, sizeof canary);
  long calls = 0, mism = 0, errmism = 0;
  for (size_t k = 0; k < NF; k++) {          /* pass 1 */
    const struct fn *f = &fns[k];
    long m = nspecial(f) + n, eset = 0;
    uint64_t h = 1469598103934665603ULL;
    R[k] = malloc(maxin * 8); E[k] = malloc(maxin * sizeof(int)); cnt[k] = m;
    for (long i = 0; i < m; i++) {
      uint64_t a, b; int e1, e2;
      input(f, i, &a, &b);
      uint64_t r1 = call(f, a, b, &e1), r2 = call(f, a, b, &e2);
      calls += 2;
      if (r1 != r2) {
        mism++;
        printf("MISMATCH %s(%016llx, %016llx): %016llx then %016llx\n", f->name,
               (unsigned long long) a, (unsigned long long) b,
               (unsigned long long) r1, (unsigned long long) r2);
      }
      if (e1 != e2) errmism++;
      if (e1) eset++;
      R[k][i] = r1; E[k][i] = e1;
      h = (h ^ r1) * 1099511628211ULL;
    }
    printf("fn %s calls %ld errno_set %ld hash %016llx\n", f->name, 2 * m, eset,
           (unsigned long long) h);
  }
  long total = 0;                            /* pass 2: shuffled */
  for (size_t k = 0; k < NF; k++) total += cnt[k];
  for (long j = 0; j < total; j++) {
    size_t k = rnd() % NF; long i = rnd() % cnt[k];
    uint64_t a, b; int e;
    input(&fns[k], i, &a, &b);
    uint64_t r = call(&fns[k], a, b, &e);
    calls++;
    if (r != R[k][i]) {
      mism++;
      printf("MISMATCH %s(%016llx, %016llx) in pass 2: %016llx, was %016llx\n",
             fns[k].name, (unsigned long long) a, (unsigned long long) b,
             (unsigned long long) r, (unsigned long long) R[k][i]);
    }
    if (e != E[k][i]) errmism++;
  }
  long bad = 0;
  for (size_t i = 0; i < sizeof canary; i++) bad += canary[i] != 0x5a;
  printf("summary functions %zu calls %ld result_mismatches %ld errno_mismatches %ld canary_changed %ld\n",
         NF, calls, mism, errmism, bad);
  return mism || errmism || bad;
}
