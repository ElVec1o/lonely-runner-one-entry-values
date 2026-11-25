// gap.c: all primitive N-subsets of [1,Vmax] with ML <= NUM/DEN, each with its exact ML (rational).
// ML(v) = max over candidate times n/(v_i+v_j), i<=j, of min_k fold(n v_k mod S)/S  (standard pair-sum candidate set).
// usage: gap N NUM DEN Vmax
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int N, NUM, DEN, Vmax; static ll v[16]; static ll found = 0, total = 0;
static ll gcdl(ll a, ll b) { while (b) { ll t = a % b; a = b; b = t; } return a; }
static int has_witness(void) {
  for (int i = N - 1; i >= 0; i--) for (int j = i; j >= 0; j--) {
    ll S = v[i] + v[j];
    for (ll n = 1; 2 * n <= S; n++) {
      int ok = 1;
      for (int k = 0; k < N; k++) { ll t = (n * v[k]) % S; ll f = t < S - t ? t : S - t; if (DEN * f <= (ll)NUM * S) { ok = 0; break; } }
      if (ok) return 1;
    }
  }
  return 0;
}
static void exact(ll *num, ll *den) {
  ll bn = 0, bd = 1;
  for (int i = 0; i < N; i++) for (int j = i; j < N; j++) {
    ll S = v[i] + v[j];
    for (ll n = 1; n < S; n++) {
      ll mn = S;
      for (int k = 0; k < N; k++) { ll t = (n * v[k]) % S; ll f = t < S - t ? t : S - t; if (f < mn) mn = f; }
      if (mn * bd > bn * S) { bn = mn; bd = S; }
    }
  }
  ll g = gcdl(bn, bd); *num = bn / g; *den = bd / g;
}
static void rec(int d, int start, ll g) {
  if (d == N) {
    if (g != 1) return;
    total++;
    if (!has_witness()) { ll a, b; exact(&a, &b); found++; printf("SET %lld/%lld :", a, b); for (int k = 0; k < N; k++) printf(" %lld", v[k]); printf("\n"); }
    return;
  }
  for (int x = start; x <= Vmax - (N - 1 - d); x++) { v[d] = x; rec(d + 1, x + 1, gcdl(g, x)); }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); NUM = atoi(argv[2]); DEN = atoi(argv[3]); Vmax = atoi(argv[4]);
  rec(0, 1, 0);
  printf("DONE N=%d tau=%d/%d Vmax=%d primitive_subsets=%lld with_ML<=tau=%lld\n", N, NUM, DEN, Vmax, total, found);
  return 0;
}
