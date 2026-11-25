// prop13.rs : falsification of BF_paper Prop 1.3 and of the assembled Theorem FS1 (own code, exact integers; 2026-11-25).
// Modes:  arith N0 N1   : arithmetic of Prop 1.3 over all N in [N0,N1], N/2<r<=N, m in [2, 4N+10]
//         fs1 N0 N1 WMAX: for N in [N0,N1], every r in [1,N], every w in (N, WMAX]: exact ML of [N]_{r->w}, check the FS1 dichotomy
use std::env;

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }

fn beta(n: i64, r: i64) -> i64 { let s = n + 1 - r; let mut b = s; while gcd(b, r) != 1 { b += 1; } b }

fn ml_exact(v: &[i128]) -> (i128, i128) {
    let mut ls: Vec<i128> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ls.push(v[i] + v[j]); } }
    ls.sort(); ls.dedup();
    let (mut bn, mut bd) = (0i128, 1i128);
    for &l in &ls {
        for k in 0..=(l / 2) {
            let mut m = i128::MAX;
            for &a in v {
                let x = (a * k) % l;
                let d = if x < l - x { x } else { l - x };
                if d < m { m = d; if m * bd <= bn * l { break; } }
            }
            if m * bd > bn * l { bn = m; bd = l; }
        }
    }
    fn g(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { g(b, a % b) } }
    let gg = g(bn, bd);
    (bn / gg, bd / gg)
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a.get(1).map(|s| s.as_str()).unwrap_or("") {
        "arith" => {
            let n0: i64 = a[2].parse().unwrap(); let n1: i64 = a[3].parse().unwrap();
            let (mut total, mut nontight, mut below, mut viol, mut s1k, mut klt0, mut kmax_ratio_num, mut kmax_ratio_den) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0i64, 1i64);
            let (mut tight_big_k, mut ex_big) = (0u64, String::new());
            let mut ex_klt0 = String::new();
            let mut strict_fail = 0u64; let mut beta_bad = 0u64; let mut ident_bad = 0u64;
            for n in n0..=n1 {
                for r in (n / 2 + 1)..=n {
                    if !(n < 2 * r) { continue; }
                    let s = n + 1 - r; let b = beta(n, r);
                    if b > n || b > r + 1 || b < s { beta_bad += 1; }
                    for m in 2..=(4 * n + 10) {
                        total += 1;
                        let k = b - m * (s - 1);          // m r + beta = m N + k
                        if m * r + b != m * n + k { ident_bad += 1; }
                        // identity: m/(m r+beta) < 1/N  <=>  k >= 1  (integers)
                        let lt = m * n < m * r + b;
                        if lt != (k >= 1) { ident_bad += 1; }
                        if m * s > b {
                            nontight += 1;
                            if k <= 0 { klt0 += 1; if ex_klt0.is_empty() { ex_klt0 = format!("N={} r={} m={} s={} beta={} k={}", n, r, m, s, b, k); } }
                            if lt { below += 1; }
                            // Prop 1.3 conclusion when ML<1/N (k>=1): 1<=k, 2k<=N; s=1 => k=1; s>=2 => k*s<beta
                            if k >= 1 {
                                let ok = 2 * k <= n && (if s == 1 { k == 1 } else { k * s < b });
                                if !ok { viol += 1; println!("VIOLATION N={} r={} m={} s={} beta={} k={}", n, r, m, s, b, k); }
                                if s == 1 { s1k += 1; }
                                // track max of 2k/N
                                if 2 * k * kmax_ratio_den > kmax_ratio_num * n { kmax_ratio_num = 2 * k; kmax_ratio_den = n; }
                                if 2 * k == n { strict_fail += 1; }
                            }
                            // the weaker general fact valid for every k (also k<=0): k*s < beta when s>=2
                            if s >= 2 && !(k * s < b) { viol += 1; println!("VIOLATION(ks<beta) N={} r={} m={}", n, r, m); }
                        } else {
                            // tight regime ms <= beta: Prop 1.3 hypothesis fails; does the conclusion fail?
                            if k >= 1 && 2 * k > n { tight_big_k += 1; if ex_big.is_empty() { ex_big = format!("N={} r={} m={} s={} beta={} k={} (2k>N)", n, r, m, s, b, k); } }
                        }
                    }
                }
            }
            println!("ARITH N in [{},{}]: total (N,r,m) triples = {}", n0, n1, total);
            println!("  hypothesis ms>beta holds: {}; of which ML<1/N (k>=1): {}; of which k<=0 (ML>=1/N): {}  e.g. {}", nontight, below, klt0, ex_klt0);
            println!("  Prop 1.3 conclusion violations (1<=k, 2k<=N; s=1=>k=1; s>=2=>k*s<beta): {}", viol);
            println!("  s=1 cases with k>=1: {}; cases with 2k==N exactly (k>=1, ms>beta): {}; max 2k/N = {}/{}", s1k, strict_fail, kmax_ratio_num, kmax_ratio_den);
            println!("  hypothesis ms>beta DROPPED (tight regime ms<=beta): triples with k>=1 and 2k>N: {}  e.g. {}", tight_big_k, ex_big);
            println!("  Lemma 1 (s<=beta<=min(N,r+1)) violations: {}; identity m r+beta=mN+k and (m/(mr+beta)<1/N <=> k>=1) violations: {}", beta_bad, ident_bad);
        }
        "fs1" => {
            let n0: i64 = a[2].parse().unwrap(); let n1: i64 = a[3].parse().unwrap(); let wmax: i64 = a[4].parse().unwrap();
            let (mut sets, mut ge, mut tight, mut shape, mut bad) = (0u64, 0u64, 0u64, 0u64, 0u64);
            let mut minkpos = (i128::MAX, 0i128);
            for n in n0..=n1 {
                for r in 1..=n {
                    for w in (n + 1)..=wmax {
                        let mut v: Vec<i128> = (1..=n).filter(|&x| x != r).map(|x| x as i128).collect();
                        v.push(w as i128);
                        let (mn, md) = ml_exact(&v);
                        sets += 1;
                        let nn = n as i128;
                        if mn * nn >= md { ge += 1; continue; }            // ML >= 1/N
                        // ML < 1/N : must be 1/(N+1) or m/(mN+k) with 1<=k, 2k<=N, and (2r>N, r | w)
                        if md == mn * (nn + 1) { tight += 1; if !(2 * r > n && w % r == 0) { bad += 1; println!("BAD tight outside branch N={} r={} w={}", n, r, w); } continue; }
                        // find sigma,k with value = sigma/(sigma N + k): sigma = mn*g, den = md*g ; k = den - sigma N must satisfy 1<=k, 2k<=N for the reduced or some multiple
                        let mut ok = false;
                        // value mn/md in lowest terms; the shape sigma/(N sigma + k) with integer sigma>=1: sigma = mn*t, md*t = N*sigma + k => k = t(md - N mn)
                        let d = md - nn * mn; // = k/t >= 1 since ML<1/N
                        if d >= 1 { let k = d; if 2 * k <= nn { ok = true; } }
                        if ok { shape += 1; if (2 * r > n && w % r == 0) == false { bad += 1; println!("BAD value<1/N outside branch N={} r={} w={} ML={}/{}", n, r, w, mn, md); } } else { bad += 1; println!("BAD shape N={} r={} w={} ML={}/{}", n, r, w, mn, md); }
                        if (d as i128) < minkpos.0 { minkpos = (d, n as i128); }
                    }
                }
            }
            println!("FS1 N in [{},{}] r in [1,N] w in (N,{}]: sets={} ML>=1/N: {} ; ML=1/(N+1) tight: {} ; ML<1/N with shape sigma/(sigma N+k), 1<=k<=N/2 (reduced k): {} ; BAD: {}", n0, n1, wmax, sets, ge, tight, shape, bad);
        }
        _ => eprintln!("usage: prop13 arith N0 N1 | fs1 N0 N1 WMAX"),
    }
}
