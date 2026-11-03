/* Exhaustive check of the interval form of ML-DSA-87 UseHint (FIPS 204 Algorithms 36-40):
 * for every r in Z_q and every u in 0..15, "some h in {0,1} has UseHint(h,r) = u" must hold exactly when
 * e = centered_q(r - a*u) lies in [-a+1-[u=0], a+[u=15]], and then h must be unique and equal to
 * [e outside [-g+1-[u=0], g]]. q = 8380417, g = gamma2 = (q-1)/32, a = 2g. */
#include <stdio.h>
#include <stdint.h>
#define Q 8380417
#define G 261888
#define A 523776
static int64_t modpm(int64_t x, int64_t m) { int64_t r = ((x % m) + m) % m; if (r > m / 2) r -= m; return r; }
static void decompose(int64_t r, int64_t *r1, int64_t *r0) {
  int64_t rp = ((r % Q) + Q) % Q, lo = modpm(rp, 2 * G);
  if (rp - lo == Q - 1) { *r1 = 0; *r0 = lo - 1; } else { *r1 = (rp - lo) / (2 * G); *r0 = lo; }
}
static int64_t usehint(int h, int64_t r) {
  int64_t r1, r0; decompose(r, &r1, &r0);
  if (h == 1 && r0 > 0) return (r1 + 1) % 16;
  if (h == 1 && r0 <= 0) return (r1 + 15) % 16;
  return r1;
}
int main(void) {
  uint64_t checks = 0, bad = 0, unique_fail = 0, hint_fail = 0, exists_count = 0;
  for (int64_t r = 0; r < Q; r++) {
    for (int u = 0; u < 16; u++) {
      int ok0 = usehint(0, r) == u, ok1 = usehint(1, r) == u;
      int exists = ok0 || ok1;
      int64_t e = modpm(r - (int64_t)A * u, Q);
      int lo = -A + 1 - (u == 0), hi = A + (u == 15);
      int claim = e >= lo && e <= hi;
      checks++;
      if (exists != claim) bad++;
      if (exists) {
        exists_count++;
        if (ok0 && ok1) unique_fail++;
        int hc = !(e >= -G + 1 - (u == 0) && e <= G);
        int htrue = ok1 ? 1 : 0;
        if (hc != htrue) hint_fail++;
      }
    }
  }
  printf("comparisons %llu, existence mismatches %llu, non-unique hints %llu, hint-rule mismatches %llu (over %llu existing cases)\n",
    (unsigned long long)checks, (unsigned long long)bad, (unsigned long long)unique_fail, (unsigned long long)hint_fail, (unsigned long long)exists_count);
  return (bad || unique_fail || hint_fail) ? 1 : 0;
}
