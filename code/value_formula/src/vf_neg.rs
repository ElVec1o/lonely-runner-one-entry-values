// vf.rs (the accompanying code, 2026-11-24).  rustc -O vf.rs -o ../bin/vf
// Independent exact check of Statement V:  for N>=2, N/2<r<=N, m>=2, s=N+1-r, beta=least integer >= s coprime to r,
//   ML([N]_{r->mr}) = max( 1/(N+1), m/(m r + beta) ).
// Method (different from gl/gf/cov; it follows the PROOF, not the search):
//   lower: explicit witness time  t = a/D (a r = -1 mod D, D = m r + beta)  if m(N+1) >= D,  else t = 1/(N+1).
//          Every runner's distance is evaluated in exact integers and must be >= claim.
//   upper: closed arcs {t : ||t v|| <= claim} must cover the circle (sorted sweep, i128 cross-multiplication).
//   negative control: with the claim lowered to claim*(1 - 1/1000) the arcs must FAIL to cover (so the claim is sharp
//   and the sweep is not vacuous), and with the claim raised to claim*(1+1/1000) the witness time must FAIL the lower test
//   (so the lower test is not vacuous).
// usage: vf NMIN NMAX MMIN MMAX
use std::env;
fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn fold(r: i128, s: i128) -> i128 { if 2 * r > s { s - r } else { r } }
// does min_v ||t v|| >= num/den hold at t = n/S ?
fn lower_ok(v: &[i128], n: i128, s: i128, num: i128, den: i128) -> bool {
    v.iter().all(|&w| fold((n * w) % s, s) * den >= num * s)
}
// do closed arcs {||t v|| <= num/den} cover the circle?
fn cover(v: &[i128], num: i128, den: i128) -> bool {
    let mut arcs: Vec<(i128, i128, i128)> = Vec::new();
    for &w in v { for j in 0..=w { arcs.push((j * den - num, j * den + num, den * w)); } }
    arcs.sort_by(|p, q| (p.0 * q.2).cmp(&(q.0 * p.2)));
    let (mut rn, mut rd) = (0i128, 1i128);
    for &(st, en, d) in arcs.iter() {
        if st * rd > rn * d { return false; }
        if en * rd > rn * d { rn = en; rd = d; }
        if rn >= rd { return true; }
    }
    rn >= rd
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let (nmin, nmax, mmin, mmax): (i128, i128, i128, i128) = (a[1].parse().unwrap(), a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap());
    let (mut tot, mut tight, mut bad) = (0u64, 0u64, 0u64);
    for n in nmin..=nmax {
        for r in (n / 2 + 1)..=n {
            let s = n + 1 - r;
            let mut beta = s; while gcd(beta, r) != 1 { beta += 1; } beta += 1; while gcd(beta, r) != 1 { beta += 1; }
            for m in mmin.max(2)..=mmax {
                let d = m * r + beta;
                // claim = max(1/(n+1), m/d)
                let (num0, den0) = if m * (n + 1) >= d { (m, d) } else { (1, n + 1) };
                let g = gcd(num0, den0); let (num, den) = (num0 / g, den0 / g);
                let mut v: Vec<i128> = (1..=n).filter(|&x| x != r).collect(); v.push(m * r);
                // witness time
                let (wn, ws) = if m * (n + 1) >= d {
                    let mut aa = 1i128; while (aa * r + 1) % d != 0 { aa += 1; if aa >= d { panic!("no inverse N={} r={} m={}", n, r, m); } }
                    (aa, d)
                } else { (1, n + 1) };
                let lo = lower_ok(&v, wn, ws, num, den);
                let up = cover(&v, num, den);
                // negative controls
                let up_neg = cover(&v, num * 999, den * 1000);   // claim lowered: must NOT cover
                let lo_neg = lower_ok(&v, wn, ws, num * 1001, den * 1000); // claim raised: witness must fail
                tot += 1; if num * (n + 1) == den { tight += 1; }
                if !(lo && up && !up_neg && !lo_neg) {
                    bad += 1; println!("FAIL N={} r={} m={} claim={}/{} lower={} cover={} negcover_fails={} neglower_fails={}", n, r, m, num, den, lo, up, !up_neg, !lo_neg);
                }
            }
        }
        if n % 10 == 0 { eprintln!("N={} done tot={} bad={}", n, tot, bad); }
    }
    println!("DONE vf N={}..{} m={}..{} instances={} tight={} failures={}", nmin, nmax, mmin, mmax, tot, tight, bad);
}
