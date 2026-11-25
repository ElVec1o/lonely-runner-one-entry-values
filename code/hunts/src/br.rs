// small exact tests for the strengthening ideas.
// Subcommands:
//   g N1 N2 CAPEXP        per-speed coverage sums G(w)=sum_D cov_w(D) (exact integer overlaps), primes D in [N+1+r,2N-1]
//   ctl                   controls for the decision engine
//   sp N1 N2 k c trials seed mode   random/adversarial test of the linear statement with T=c*k+1 primes (mode 0: level 1/N, primes in window; mode 1: level 2/(D_T+1), first T primes >= N+1+r)
//   hunt N1 N2 kmax wmax  lower-bound hunt for exceptions (individually killing speeds <= wmax)
//   liu N1 N2             ML([M]\{r}) >= / < checks against 2/D0 (decision at 2/D0 true, at 2/(D0-1)... false)
use std::collections::HashSet;
type I = i128;
fn gcd(a: I, b: I) -> I { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn is_prime(n: I) -> bool { if n < 2 { return false; } let mut d = 2; while d * d <= n { if n % d == 0 { return false; } d += 1; } true }
fn inv_mod(a: I, m: I) -> I { // a^{-1} mod m, gcd=1
    let (mut r0, mut r1, mut s0, mut s1) = (m, a.rem_euclid(m), 0 as I, 1 as I);
    while r1 != 0 { let q = r0 / r1; let t = r0 - q * r1; r0 = r1; r1 = t; let t = s0 - q * s1; s0 = s1; s1 = t; }
    s0.rem_euclid(m)
}
// exact overlap of [cm-h, cm+h] with the union of (nP-R, nP+R), n in Z (R <= P/2 so they are disjoint)
fn overlap(cm: I, h: I, p: I, r: I) -> I {
    let lo = cm - h; let hi = cm + h;
    let mut n = (lo - r).div_euclid(p); let mut tot = 0;
    loop { let a = n * p - r; let b = n * p + r; if a >= hi { break; }
        let x = lo.max(a); let y = hi.min(b); if y > x { tot += y - x; } n += 1; }
    tot
}
// coverage fraction (num, den) of J(D)=[t0 +- delta] by the bad set of w at level 1/N.
// dep: delta=(2N-D)/(D N^2).  fix: delta=1/((2N-1)N^2).
fn cov(n: I, d: I, y: I, w: I, fix: bool) -> (I, I) {
    if !fix { let p = d * n * n; let r = d * n; let h = (2 * n - d) * w; (overlap(n * n * y, h, p, r), 2 * h) }
    else { let k = 2 * n - 1; let p = d * k * n * n; let r = d * k * n; let h = d * w; (overlap(k * n * n * y, h, p, r), 2 * h) }
}
#[derive(Clone, Copy)]
struct Fr(I, I);
fn le(a: Fr, b: Fr) -> bool { a.0 * b.1 <= b.0 * a.1 }
fn mx(a: Fr, b: Fr) -> Fr { if le(a, b) { b } else { a } }
fn mn(a: Fr, b: Fr) -> Fr { if le(a, b) { a } else { b } }
// intersect cur (closed intervals in [0,1/2]) with {t: ||v t|| >= p/q}
fn step(cur: &Vec<(Fr, Fr)>, v: I, p: I, q: I) -> Vec<(Fr, Fr)> {
    let mut out = Vec::new();
    for &(lo, hi) in cur {
        let mut n = ((lo.0 * v).div_euclid(lo.1) - 1).max(0);
        loop { let a = Fr(n * q + p, q * v); if !le(a, hi) { break; }
            let b = Fr((n + 1) * q - p, q * v);
            let x = mx(lo, a); let y = mn(hi, b); if le(x, y) { out.push((x, y)); } n += 1; }
    }
    out
}
fn good_set(speeds: &[I], p: I, q: I) -> Vec<(Fr, Fr)> {
    let mut cur = vec![(Fr(0, 1), Fr(1, 2))];
    for &v in speeds { cur = step(&cur, v, p, q); if cur.is_empty() { break; } }
    cur
}
fn base(n: I, r: I) -> Vec<I> { (1..=n).filter(|&x| x != r).collect() }
fn has_good(n: I, r: I, w: &[I], p: I, q: I) -> bool {
    let mut s = base(n, r); let mut ww = w.to_vec(); ww.sort(); s.extend(ww); !good_set(&s, p, q).is_empty()
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, m: u64) -> u64 { self.next() % m } }
fn crt(res: &[(I, I)]) -> (I, I) { // (x, M) with x = r_i mod m_i, moduli pairwise coprime
    let (mut x, mut m) = (0 as I, 1 as I);
    for &(r, mi) in res { let t = ((r - x).rem_euclid(mi) * inv_mod(m.rem_euclid(mi), mi)).rem_euclid(mi); x += m * t; m *= mi; }
    (x, m)
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let num = |i: usize| -> I { a[i].parse().unwrap() };
    match a[1].as_str() {
        "g" => {
            let (n1, n2, capexp) = (num(2), num(3), num(4));
            println!("# per-speed coverage sums; columns: N  #r  maxG_dep (r,w)  maxG_fix (r,w)  max N*cov_dep over w>=3.5N^2  max#fullkill_dep (r,w)");
            for n in n1..=n2 {
                let wmax = if capexp == 3 { n * n * n } else { 4 * n * n };
                let (mut bd, mut bf, mut osc, mut fk) = ((0f64, 0, 0), (0f64, 0, 0), 0f64, (0usize, 0, 0));
                for r in 1..=n / 2 {
                    let ds: Vec<(I, I)> = (n + 1 + r..=2 * n - 1).filter(|&d| is_prime(d)).map(|d| (d, inv_mod(r, d))).collect();
                    if ds.is_empty() { continue; }
                    for w in n + 1..=wmax {
                        let (mut gd, mut gf, mut full) = (0f64, 0f64, 0usize);
                        for &(d, ai) in &ds {
                            let y = (ai * w) % d;
                            let (x, l) = cov(n, d, y, w, false); let c = x as f64 / l as f64; gd += c; if x == l { full += 1; }
                            if w * 2 >= 7 * n * n && c * n as f64 > osc { osc = c * n as f64; }
                            let (x, l) = cov(n, d, y, w, true); gf += x as f64 / l as f64;
                        }
                        if gd > bd.0 { bd = (gd, r, w); } if gf > bf.0 { bf = (gf, r, w); } if full > fk.0 { fk = (full, r, w); }
                    }
                }
                println!("{} {} {:.4} ({},{}) {:.4} ({},{}) {:.3} {} ({},{})", n, n / 2, bd.0, bd.1, bd.2, bf.0, bf.1, bf.2, osc, fk.0, fk.1, fk.2);
            }
        }
        "ctl" => {
            let t = |n: I, r: I, w: &[I], p: I, q: I, exp: bool| { let g = has_good(n, r, w, p, q); println!("N={} r={} W={:?} level {}/{}: good={} expected={} {}", n, r, w, p, q, g, exp, if g == exp { "OK" } else { "MISMATCH" }); };
            t(13, 6, &[69], 3, 40, true); t(13, 6, &[69], 1, 13, false); t(13, 6, &[69], 31, 400, false);
            t(20, 6, &[29, 31], 2, 41, true); t(20, 6, &[29, 31], 1, 20, false); t(21, 6, &[29, 31], 1, 21, true);
            t(8, 9, &[], 1, 9, true); t(8, 9, &[], 10, 89, false); // [8]: ML=1/9
            t(30, 7, &[48], 2, 43, true); t(5, 1, &[], 2, 7, true); t(5, 1, &[], 21, 70, false);
        }
        "liu" => { // ML([M]\{r}) = 2/D0, D0 least integer >= M+1+r coprime to r (r <= M/2): decision true at 2/D0, false at (2*D0+1)/(D0*D0) (slightly above)
            let (n1, n2) = (num(2), num(3)); let (mut ok, mut bad) = (0, 0);
            for m in n1..=n2 { for r in 1..=m / 2 { let mut d0 = m + 1 + r; while gcd(d0, r) != 1 { d0 += 1; }
                let g1 = has_good(m, r, &[], 2, d0); let g2 = has_good(m, r, &[], 2 * d0 + 1, d0 * d0);
                if g1 && !g2 { ok += 1; } else { bad += 1; println!("LIU MISMATCH M={} r={} D0={} {} {}", m, r, d0, g1, g2); } } }
            println!("liu M={}..{}: ok={} mismatch={}", n1, n2, ok, bad);
        }
        "sp" => {
            let (n1, n2, k, c, trials, seed, mode) = (num(2), num(3), num(4), num(5), num(6), num(7), num(8));
            let mut rng = Rng(seed as u64 * 2654435761 + 88172645463325252);
            let (mut tested, mut fails, mut skipped) = (0u64, 0u64, 0u64);
            let t = (c * k + 1) as usize;
            for n in n1..=n2 { for r in 1..=(if mode == 0 { n / 2 } else { n - 2 }) {
                let ps: Vec<I> = if mode == 0 { (n + 1 + r..=2 * n - 1).filter(|&d| is_prime(d)).collect() } else { (n + 1 + r..).filter(|&d| is_prime(d)).take(t).collect() };
                if ps.len() < t { skipped += 1; continue; }
                let (p, q) = if mode == 0 { (1, n) } else { (2, ps[t - 1] + 1) };
                let npr = if mode == 0 { ps.len() } else { t };
                for _ in 0..trials {
                    // adversarial W: each speed solves w = e_i r (mod D_i) for 1..3 distinct primes of the family, e_i in {-2..2}; small lift
                    let mut w: Vec<I> = Vec::new(); let mut used: Vec<usize> = Vec::new();
                    for _ in 0..k {
                        let cnt = 1 + rng.below(3) as usize; let mut res = Vec::new();
                        for _ in 0..cnt { let mut i = rng.below(npr as u64) as usize; let mut tries = 0;
                            while (used.contains(&i) || res.iter().any(|&(_, m)| m == ps[i])) && tries < 50 { i = rng.below(npr as u64) as usize; tries += 1; }
                            if res.iter().any(|&(_, m)| m == ps[i]) { continue; }
                            used.push(i); let e = rng.below(5) as I - 2; res.push(((e * r).rem_euclid(ps[i]), ps[i])); }
                        let (x, m) = crt(&res); let mut v = x + m * (rng.below(3) as I); while v <= n { v += m; }
                        if rng.below(8) == 0 { v = n + 1 + rng.below((4 * n) as u64) as I; }
                        if v > 4_000_000_000 { v = x + m; if v > 4_000_000_000 { v = n + 1 + rng.below((n * n) as u64) as I; } }
                        if !w.contains(&v) { w.push(v); }
                    }
                    tested += 1;
                    if !has_good(n, r, &w, p, q) { fails += 1; if fails <= 12 { println!("FAIL N={} r={} W={:?} level {}/{} #primes={}", n, r, w, p, q, ps.len()); } }
                } } }
            println!("sp N={}..{} k={} c={} T={} mode={} : tested={} FAIL={} (N,r) skipped for too few primes={}", n1, n2, k, c, t, mode, tested, fails, skipped);
        }
        "hunt" => {
            let (n1, n2, kmax, wmax) = (num(2), num(3), num(4) as usize, num(5));
            println!("# hunt: N  min k (<=kmax) of an exception with individually killing speeds <= wmax, r <= N/2 ; lower bound evidence only");
            for n in n1..=n2 {
                let mut best: (usize, I, Vec<I>) = (99, 0, vec![]);
                for r in 1..=n / 2 {
                    let g0 = good_set(&base(n, r), 1, n); let m = g0.len(); if m == 0 || m > 120 { continue; }
                    let full: u128 = if m == 128 { !0 } else { (1u128 << m) - 1 };
                    let mut seen: HashSet<u128> = HashSet::new(); let mut masks: Vec<(u128, I)> = Vec::new();
                    for w in n + 1..=wmax { let mut mk = 0u128;
                        for (i, iv) in g0.iter().enumerate() { if step(&vec![*iv], w, 1, n).is_empty() { mk |= 1 << i; } }
                        if mk != 0 && seen.insert(mk) { masks.push((mk, w)); } }
                    // drop dominated masks
                    let mm: Vec<(u128, I)> = masks.iter().filter(|&&(x, _)| !masks.iter().any(|&(y, _)| y != x && (x & y) == x)).cloned().collect();
                    fn dfs(cov: u128, full: u128, depth: usize, lim: usize, mm: &Vec<(u128, I)>, pick: &mut Vec<I>) -> bool {
                        if cov == full { return true; } if depth == lim { return false; }
                        let unc = full & !cov; let mut bi = 0; let mut bc = usize::MAX; let mut u = unc;
                        while u != 0 { let i = u.trailing_zeros(); u &= u - 1; let c = mm.iter().filter(|&&(x, _)| x >> i & 1 == 1).count(); if c < bc { bc = c; bi = i; } }
                        if bc == 0 { return false; }
                        for &(x, w) in mm.iter() { if x >> bi & 1 == 1 { pick.push(w); if dfs(cov | x, full, depth + 1, lim, mm, pick) { return true; } pick.pop(); } }
                        false
                    }
                    for lim in 1..=kmax.min(best.0.saturating_sub(1)) { let mut pick = Vec::new(); if dfs(0, full, 0, lim, &mm, &mut pick) { best = (lim, r, pick); break; } }
                }
                if best.0 == 99 { println!("{} none<= {}", n, kmax); } else {
                    let ok = !has_good(n, best.1, &best.2, 1, n);
                    println!("{} k={} r={} W={:?} verified_below_1/N={}", n, best.0, best.1, best.2, ok); }
            }
        }
        "fam" => { // W = all D in (X, X+r] coprime to r ; report every N (2r<=N) with an X making ML<1/N ; prediction test
            let (r, n1, n2) = (num(2), num(3), num(4));
            let mut last = 0;
            for n in n1.max(2 * r)..=n2 { let mut hit: Option<(I, Vec<I>)> = None;
                for x in n..=n + 1 + 2 * r { let w: Vec<I> = (x + 1..=x + r).filter(|&d| gcd(d, r) == 1).collect();
                    if !has_good(n, r, &w, 1, n) { hit = Some((x, w)); break; } }
                if let Some((x, w)) = hit { last = n; println!("r={} N={} k={} X={} W={:?} ML<1/N", r, n, w.len(), x, w); } }
            println!("fam r={} N in {}..{}: last N with an exception of this family = {}", r, n1.max(2 * r), n2, last);
        }
        _ => { println!("unknown"); }
    }
}
