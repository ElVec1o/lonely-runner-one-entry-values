// gf.rs: exact checks of one-entry modifications [N]_{r->w} = ([1..N] \ {r}) u {w}.  rustc -O gf.rs
//   gf fam NMAX MMAX        : w = m r (2<=m<=MMAX): compare exact ML with the closed form m/(m r + min(beta, m s)),
//                             s = N+1-r, beta = least integer >= s coprime to r.   Prints every mismatch and a per-N summary.
//   gf one NMIN NMAX WMULT  : all w in [N+1, WMULT*N]: list every [N]_{r->w} with 1/(N+1) < ML < 2/(2N+1), and tight ones.
use std::env;
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
#[inline] fn fold(r: u64, m: u64) -> u64 { if 2 * r > m { m - r } else { r } }
// exact ML; if cap=Some((cn,cd)) returns None as soon as some time has value > cn/cd
fn ml(v: &[u64], cap: Option<(u64, u64)>) -> Option<(u64, u64)> {
    let (mut bn, mut bd) = (0u64, 1u64);
    for i in 0..v.len() { for j in i..v.len() { let s = v[i] + v[j]; for n in 1..=(s / 2) {
        let mut mn = u64::MAX;
        for &x in v { let f = fold((n * x) % s, s); if f < mn { mn = f; if mn * bd <= bn * s { break; } } }
        if mn * bd > bn * s { bn = mn; bd = s; if let Some((cn, cd)) = cap { if bn * cd > cn * bd { return None; } } }
    } } }
    let g = gcd(bn, bd); Some((bn / g, bd / g))
}
fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() >= 4 && a[1] == "fam" {
        let nmax: u64 = a[2].parse().unwrap(); let mmax: u64 = a[3].parse().unwrap();
        let (mut tot, mut bad, mut tight) = (0u64, 0u64, 0u64);
        for n in 3..=nmax {
            let mut best: Option<(u64, u64, u64, u64)> = None; // smallest non-tight value (num, den, r, m)
            for r in 1..=n { let s = n + 1 - r; for m in 2..=mmax { let w = m * r; if w <= n { continue; }
                let mut v: Vec<u64> = (1..=n).filter(|&x| x != r).collect(); v.push(w);
                let (en, ed) = ml(&v, None).unwrap();
                let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
                let d = m * r + beta.min(m * s); let g = gcd(m, d); let (pn, pd) = (m / g, d / g);
                tot += 1;
                if (en, ed) != (pn, pd) { bad += 1; println!("MISMATCH N={} r={} m={} w={} exact={}/{} formula={}/{} beta={}", n, r, m, w, en, ed, pn, pd, beta); }
                if en * (n + 1) == ed { tight += 1; } else if best.map_or(true, |(bn, bd, _, _)| en * bd < bn * ed) { best = Some((en, ed, r, m)); }
            } }
            if let Some((bn, bd, r, m)) = best {
                let below2 = bn * (2 * n + 1) < 2 * bd;
                // Stab: value >= 1/(N+1) + 1/(4N^2)  <=>  bn*4N^2(N+1) >= bd*(4N^2 + N + 1)
                let stab_ok = bn * 4 * n * n * (n + 1) >= bd * (4 * n * n + n + 1);
                println!("N={} min non-tight in family m<= {}: {}/{} at r={} m={} (w={})  below 2/(2N+1): {}  Stab holds: {}", n, mmax, bn, bd, r, m, m * r, below2, stab_ok);
            }
        }
        println!("DONE fam NMAX={} MMAX={} sets={} tight={} mismatches={}", nmax, mmax, tot, tight, bad);
        return;
    }
    if a.len() >= 3 && a[1] == "pred" {
        // closed-form prediction (CONJECTURED beyond the verified range): G(N) = min over N/2 < r <= N of m/(m r + beta), m = floor(beta/s)+1
        let nmax: u64 = a[2].parse().unwrap();
        for n in 4..=nmax { let mut best = (2u64, 2 * n + 1, n, 2u64, 1u64);
            for r in (n / 2 + 1)..=n { let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
                let m = beta / s + 1; let (pn, pd) = (m, m * r + beta);
                if pn * best.1 < best.0 * pd { best = (pn, pd, r, m, beta); } }
            let g = gcd(best.0, best.1); let (bn, bd) = (best.0 / g, best.1 / g);
            let stab_ok = bn * 4 * n * n * (n + 1) >= bd * (4 * n * n + n + 1);
            if bn * (2 * n + 1) < 2 * bd { println!("PRED N={} G={}/{} r={} m={} beta={} s={} Stab_holds={}", n, bn, bd, best.2, best.3, best.4, n + 1 - best.2, stab_ok); } }
        return;
    }
    if a.len() >= 5 && a[1] == "one" {
        let nmin: u64 = a[2].parse().unwrap(); let nmax: u64 = a[3].parse().unwrap(); let wm: u64 = a[4].parse().unwrap();
        for n in nmin..=nmax { let mut cnt = 0u64; let mut hits = 0;
            for r in 1..=n { for w in (n + 1)..=(wm * n) {
                let mut v: Vec<u64> = (1..=n).filter(|&x| x != r).collect(); v.push(w); cnt += 1;
                // cap just below 2/(2N+1): values <= (2*K-1)/((2N+1)*K) with K large  (strictly below 2/(2N+1) for our denominators)
                if let Some((en, ed)) = ml(&v, Some((2 * 1000003 - 1, (2 * n + 1) * 1000003))) {
                    hits += 1; let t = if en * (n + 1) == ed { "TIGHT" } else { "NEAR" };
                    println!("{} N={} r={} w={} ML={}/{}", t, n, r, w, en, ed); } } }
            println!("DONE one N={} w<={} sets={} hits(below 2/(2N+1))={}", n, wm * n, cnt, hits); }
        return;
    }
}
