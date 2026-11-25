// dens.rs: d_s = natural density of {r : gcd(b,r) > 1 for every b in [s,2s-1]}.
// Exact (f64 sums over covering sets of primes < 2s) for s <= SE; for s > SE only the upper bound 1/Pi_s, Pi_s = prod primes in [s,2s-1].
//   dens SE SMAX
use std::env;
fn main() {
    let a: Vec<String> = env::args().collect();
    let se: usize = a[1].parse().unwrap(); let smax: usize = a[2].parse().unwrap();
    let lim = 2 * smax + 2;
    let mut comp = vec![false; lim + 1]; let mut th = vec![0f64; lim + 1];
    for i in 2..=lim { if !comp[i] { let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } th[i] = th[i - 1] + if !comp[i] { (i as f64).ln() } else { 0.0 }; }
    let mut sum_exact = 0.0; let mut sum_bound_tail = 0.0; let mut cum = vec![];
    for s in 2..=smax {
        let lnpi = th[2 * s - 1] - th[s - 1]; let bound = (-lnpi).exp();
        if s <= se {
            let primes: Vec<usize> = (2..2 * s).filter(|&p| !comp[p]).collect(); let k = primes.len();
            let masks: Vec<u64> = (s..2 * s).map(|b| { let mut m = 0u64; for (i, &p) in primes.iter().enumerate() { if b % p == 0 { m |= 1 << i; } } m }).collect();
            let mut d = 0.0f64; let mut minprod = f64::MAX; let mut minq = 0u64;
            for q in 0u64..(1u64 << k) {
                if masks.iter().all(|&mk| mk & q != 0) {
                    let mut w = 1.0; let mut pr = 1.0; for i in 0..k { let p = primes[i] as f64; if (q >> i) & 1 == 1 { w *= 1.0 / p; pr *= p; } else { w *= 1.0 - 1.0 / p; } }
                    d += w; if pr < minprod { minprod = pr; minq = q; }
                }
            }
            let minp: Vec<usize> = (0..k).filter(|&i| (minq >> i) & 1 == 1).map(|i| primes[i]).collect();
            sum_exact += d; cum.push((s, sum_exact));
            println!("s={:>3} d_s(exact)={:.8e} 1/Pi_s={:.3e} min covering product={} primes={:?}", s, d, bound, minprod, minp);
        } else { sum_bound_tail += bound; }
    }
    println!("SUM_{{s=2..{}}} d_s (exact) = {:.8}", se, sum_exact);
    println!("SUM_{{s={}..{}}} 1/Pi_s (upper bound for d_s) = {:.6e}", se + 1, smax, sum_bound_tail);
    println!("union bound on upper density of {{N: some s>=2 has forcing}} <= {:.8};  so lower density of {{G(N)=2/(2N+1)}} >= {:.8}", sum_exact + sum_bound_tail, 1.0 - sum_exact - sum_bound_tail);
    for (s, c) in cum.iter().filter(|(s, _)| [2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40].contains(s)) { println!("  partial sum to s={}: {:.8}", s, c); }
}
