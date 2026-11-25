// gtab.rs: G+(N) = min over N/2<r<=N of m_r/(m_r r + beta_r), m_r = floor(beta_r/s)+1 (smallest non-tight multiplier),
// exact fractions via u128 cross-multiplication.  usage: gtab NMIN NMAX [stride]; prints N, G+, (r,m,beta,s), N^2(G+ - 1/(N+1)) as f64 (display only).
use std::env;
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }
fn main() {
    let a: Vec<String> = env::args().collect();
    let (nmin, nmax): (u128, u128) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    let all = a.len() > 3;
    let mut minval = f64::MAX; let mut minn = 0;
    for n in nmin..=nmax {
        let mut best: (u128, u128, u128, u128, u128) = (1, 0, 0, 0, 0); // num, den, r, m, beta ; den==0 means none
        for r in (n / 2 + 1)..=n {
            let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
            let m = beta / s + 1; let (pn, pd) = (m, m * r + beta);
            if best.1 == 0 || pn * best.1 < best.0 * pd { best = (pn, pd, r, m, beta); }
        }
        let (bn, bd, r, m, beta) = best; let g = gcd(bn, bd);
        // excess = bn/bd - 1/(n+1) = (bn(n+1) - bd)/(bd(n+1))
        let ex_num = bn * (n + 1) - bd; let ex_den = bd * (n + 1);
        let v = (n * n) as f64 * (ex_num as f64) / (ex_den as f64);
        if n >= 6 && v < minval { minval = v; minn = n; }
        if all || [13u128, 19, 25, 31, 37, 61, 211, 2311].contains(&n) { println!("N={} G+={}/{} r={} m={} beta={} s={} excess_num/den={}/{} N^2*excess={:.6}", n, bn / g, bd / g, r, m, beta, n + 1 - r, ex_num, ex_den, v); }
    }
    println!("DONE gtab N={}..{} min N^2*excess (N>=6) = {:.6} at N={}", nmin, nmax, minval, minn);
}
