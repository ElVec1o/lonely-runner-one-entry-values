// cov.rs: independent certificate check of ML(v) = a/b by a different algorithm than gl/gf.
//   cov a b n S v1 v2 ...
// (1) lower bound: at t = n/S every runner is at distance >= a/b  (integer arithmetic)
// (2) upper bound: the closed arcs {t : ||t v_k|| <= a/b} cover [0,1] (sorted sweep, exact i128 cross-multiplication)
// negative control: with a/b replaced by a slightly smaller fraction (2) must FAIL (run by the caller).
use std::env;
fn main() {
    let x: Vec<i128> = env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (a, b, n, s) = (x[0], x[1], x[2], x[3]); let v = &x[4..];
    let lower = v.iter().all(|&w| { let r = (n * w) % s; let f = if 2 * r > s { s - r } else { r }; f * b >= a * s });
    // arcs as (num_start, num_end, den) with den = b*w
    let mut arcs: Vec<(i128, i128, i128)> = Vec::new();
    for &w in v { for j in 0..=w { arcs.push((j * b - a, j * b + a, b * w)); } }
    arcs.sort_by(|p, q| (p.0 * q.2).cmp(&(q.0 * p.2)));
    let (mut rn, mut rd) = (0i128, 1i128); let mut ok = true; let mut gap = (0i128, 1i128);
    for &(st, en, d) in arcs.iter() {
        if st * rd > rn * d { ok = false; gap = (rn, rd); break; }
        if en * rd > rn * d { rn = en; rd = d; }
        if rn >= rd { break; }
    }
    if ok && rn < rd { ok = false; gap = (rn, rd); }
    println!("cov N={} max={} claim {}/{}: lower(t={}/{})={} upper(cover)={} arcs={}{}", v.len(), v.iter().max().unwrap(), a, b, n, s, lower, ok, arcs.len(),
        if ok { String::new() } else { format!(" first uncovered just after {}/{}", gap.0, gap.1) });
}
