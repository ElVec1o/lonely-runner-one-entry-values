// Independent reviewer checker (written from the definition ML(V)=max_t min_v ||t v||).
// Exact certificate: ML(V)=tau  iff  closed arcs {||tv||<=tau} cover the circle AND open arcs {||tv||<tau} do not.
// Brute mode: ML by candidate times k/d, d in {vi+vj, |vi-vj|}, exact fractions.
use std::env;
type F = (i128, i128); // num, den>0
fn lt(a: F, b: F) -> bool { a.0 * b.1 < b.0 * a.1 }
fn le(a: F, b: F) -> bool { a.0 * b.1 <= b.0 * a.1 }
fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn beta_of(s: i64, r: i64) -> i64 { let mut b = s; while gcd(b, r) != 1 { b += 1; } b }
fn next_unit(b: i64, r: i64) -> i64 { let mut c = b + 1; while gcd(c, r) != 1 { c += 1; } c }
fn covers(v: &[i64], p: i128, q: i128, closed: bool) -> bool {
    // tau = p/q ; arc around k/v: ((k q - p)/(v q), (k q + p)/(v q)), k=0..=v
    let mut arcs: Vec<(F, F)> = Vec::new();
    for &x in v { let x = x as i128; for k in 0..=x { arcs.push(((k * q - p, x * q), (k * q + p, x * q))); } }
    arcs.sort_by(|a, b| { if lt(a.0, b.0) { std::cmp::Ordering::Less } else if lt(b.0, a.0) { std::cmp::Ordering::Greater } else { std::cmp::Ordering::Equal } });
    let mut reach: F = (0, 1);
    for a in &arcs {
        if le((1, 1), reach) { return true; }
        let ok = if closed { le(a.0, reach) } else { lt(a.0, reach) };
        if ok { if lt(reach, a.1) { reach = a.1; } } else { return false; }
    }
    le((1, 1), reach)
}
fn frac_max(a: F, b: F) -> F { if lt(a, b) { b } else { a } }
fn reduce(a: F) -> F { let g = gcd(a.0 as i64, a.1 as i64) as i128; (a.0 / g, a.1 / g) }
fn build(n: i64, r: i64, m: i64) -> Vec<i64> {
    let mut v: Vec<i64> = (1..=n).filter(|&x| x != r).collect();
    let mr = m * r; if !v.contains(&mr) { v.push(mr); } v
}
fn claim(n: i64, r: i64, m: i64, beta: i64) -> F {
    let a: F = (1, (n + 1) as i128);
    let b: F = (m as i128, (m * r + beta) as i128);
    reduce(frac_max(a, b))
}
fn brute_ml(v: &[i64]) -> F {
    let mut ds: Vec<i64> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ds.push(v[i] + v[j]); if v[i] != v[j] { ds.push((v[i] - v[j]).abs()); } } }
    ds.sort(); ds.dedup();
    let mut best: F = (0, 1);
    for &d in &ds {
        for k in 0..d {
            let mut mn = d; // min distance numerator
            for &x in v { let y = (k as i128 * x as i128 % d as i128) as i64; let dd = y.min(d - y); if dd < mn { mn = dd; if lt(((mn) as i128, d as i128), best) || ((mn as i128) * best.1 == best.0 * d as i128 && false) { break; } } }
            let c: F = (mn as i128, d as i128);
            if lt(best, c) { best = c; }
        }
    }
    reduce(best)
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a[1].as_str();
    if mode == "cover" {
        let nmax: i64 = a[2].parse().unwrap(); let mmax: i64 = a[3].parse().unwrap();
        let (mut tot, mut fail, mut tight, mut nf1, mut nf2, mut nneg, mut negfail_nextunit) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let mut distinct_nr = 0u64;
        for n in 2..=nmax { for r in 1..=n { if 2 * r <= n { continue; } distinct_nr += 1;
            let s = n + 1 - r; let beta = beta_of(s, r);
            for m in 2..=mmax {
                let v = build(n, r, m); assert!(v.len() as i64 == n);
                let c = claim(n, r, m, beta); let (p, q) = (c.0, c.1);
                tot += 1;
                let c_closed = covers(&v, p, q, true); let o_open = covers(&v, p, q, false);
                let ok = c_closed && !o_open;
                if !ok { fail += 1; println!("FAIL n={} r={} m={} claim={}/{} closedcover={} opencover={}", n, r, m, p, q, c_closed, o_open); }
                // controls: slightly below should not be covered closed ; slightly above should be covered open
                let lo = covers(&v, p * 1000 - 1, q * 1000, true); let hi = covers(&v, p * 1000 + 1, q * 1000, false);
                if lo { nf1 += 1; println!("CTRL-LO-FAIL n={} r={} m={}", n, r, m); }
                if !hi { nf2 += 1; println!("CTRL-HI-FAIL n={} r={} m={}", n, r, m); }
                if p * (n as i128 + 1) == q { tight += 1; }
                // negative control: beta replaced by next unit => claim should be wrong in most nontight cases
                let c2 = claim(n, r, m, next_unit(beta, r));
                if c2 != c { nneg += 1; let ok2 = covers(&v, c2.0, c2.1, true) && !covers(&v, c2.0, c2.1, false); if ok2 { negfail_nextunit += 1; } }
            } } }
        println!("COVER n<={} m<={} (n,r) pairs={} instances={} FAIL={} ctrlLO_fail={} ctrlHI_fail={} tight_instances={} negctrl(beta->next unit): differing claims={} of which still certified (instrument failed to discriminate)={}", nmax, mmax, distinct_nr, tot, fail, nf1, nf2, tight, nneg, negfail_nextunit);
    } else if mode == "abl" { // hypothesis ablation 2r<=N
        let nmax: i64 = a[2].parse().unwrap(); let mmax: i64 = a[3].parse().unwrap();
        let (mut tot, mut mism) = (0u64, 0u64);
        for n in 4..=nmax { for r in 2..=n { if 2 * r > n { continue; } let s = n + 1 - r; let beta = beta_of(s, r);
            for m in 2..=mmax { if m * r <= n { continue; } let v = build(n, r, m); if v.len() as i64 != n { continue; }
                let c = claim(n, r, m, beta); tot += 1;
                if !(covers(&v, c.0, c.1, true) && !covers(&v, c.0, c.1, false)) { mism += 1; if mism <= 3 { println!("ablation mismatch n={} r={} m={} claim={}/{}", n, r, m, c.0, c.1); } } } } }
        println!("ABLATION (2r<=N, mr>N) instances={} formula-not-certified={}", tot, mism);
    } else if mode == "brute" {
        let nmax: i64 = a[2].parse().unwrap(); let mmax: i64 = a[3].parse().unwrap();
        let (mut tot, mut bad) = (0u64, 0u64);
        for n in 2..=nmax { for r in 1..=n { if 2 * r <= n { continue; } let s = n + 1 - r; let beta = beta_of(s, r);
            for m in 2..=mmax { let v = build(n, r, m); let c = claim(n, r, m, beta); let b = brute_ml(&v); tot += 1;
                if b != c { bad += 1; println!("BRUTE MISMATCH n={} r={} m={} claim={}/{} brute={}/{}", n, r, m, c.0, c.1, b.0, b.1); } } } }
        println!("BRUTE n<={} m<={} instances={} mismatches={}", nmax, mmax, tot, bad);
    } else if mode == "inst" {
        let n: i64 = a[2].parse().unwrap(); let r: i64 = a[3].parse().unwrap(); let m: i64 = a[4].parse().unwrap();
        let s = n + 1 - r; let beta = beta_of(s, r); let v = build(n, r, m); let c = claim(n, r, m, beta); let b = brute_ml(&v);
        let cc = covers(&v, c.0, c.1, true); let oo = covers(&v, c.0, c.1, false);
        println!("N={} r={} m={} s={} beta={} claim={}/{} brute={}/{} closedcover={} opencover={}", n, r, m, s, beta, c.0, c.1, b.0, b.1, cc, oo);
    }
}
