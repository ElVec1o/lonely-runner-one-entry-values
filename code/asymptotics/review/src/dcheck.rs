// Fresh-session review: densities d_s of {r: gcd(b,r)>1 for all b in [s,2s-1]}.
// Method 1 (s=2..14): full-period enumeration of r in [0,D_s) (D_s = prod primes <2s), direct gcd.
// Method 2 (s=2..40): sum over covering prime subsets Q of prod_{p notin Q}(p-1), exact u128.
// Then: tail sums sum 1/Pi_s (f64, logs), Lemma 3b / Lemma 4 sanity, final lower bound.
fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }
fn primes_upto(n: usize) -> Vec<u64> { let mut s = vec![true; n + 1]; let mut v = vec![]; for i in 2..=n { if s[i] { v.push(i as u64); let mut j = i * i; while j <= n { s[j] = false; j += i; } } } v }
fn main() {
    let ps = primes_upto(80);
    let mut dsum = 0f64;
    let mut dvals = vec![0f64; 41];
    let mut nums = vec![0u128; 41]; let mut dens = vec![0u128; 41];
    for s in 2..=40u64 {
        let pr: Vec<u64> = ps.iter().cloned().filter(|&p| p < 2 * s).collect();
        let k = pr.len();
        let mut bm: Vec<u32> = vec![];
        for b in s..=(2 * s - 1) { let mut m = 0u32; for (i, &p) in pr.iter().enumerate() { if b % p == 0 { m |= 1 << i; } } bm.push(m); }
        let mut num: u128 = 0;
        for q in 0u32..(1u32 << k) {
            if bm.iter().all(|&m| m & q != 0) {
                let mut prod: u128 = 1;
                for i in 0..k { if q >> i & 1 == 0 { prod *= (pr[i] - 1) as u128; } }
                num += prod;
            }
        }
        let d: u128 = pr.iter().map(|&p| p as u128).product();
        nums[s as usize] = num; dens[s as usize] = d;
        let f = num as f64 / d as f64;
        dvals[s as usize] = f; dsum += f;
        if s <= 14 {
            // full period enumeration
            let dd = d as u64;
            let mut cnt = 0u64;
            for r in 0..dd {
                let mut ok = true;
                for b in s..=(2 * s - 1) { if gcd(b, r) == 1 { ok = false; break; } }
                if ok { cnt += 1; }
            }
            println!("s={} D={} num_subset={} num_enum={} {}", s, dd, num, cnt, if cnt as u128 == num { "EQ" } else { "MISMATCH" });
        } else if s <= 17 || s == 40 { println!("s={} D={} num={} d={:.6e}", s, d, num, f); }
        if s <= 12 { println!("   d_{} = {:.10e}   1/d = {:.4}", s, f, 1.0 / f); }
    }
    println!("HEAD sum_{{s=2..40}} d_s = {:.12}", dsum);
    // Pi_s via logs: sieve to 40000
    let pr2 = primes_upto(41000);
    let mut th = vec![0f64; 41001]; // theta(x) = sum ln p, p<=x
    for x in 1..=41000usize { th[x] = th[x - 1]; }
    { let mut acc = 0f64; let mut idx = 0; for x in 1..=41000usize { while idx < pr2.len() && pr2[idx] as usize <= x { acc += (pr2[idx] as f64).ln(); idx += 1; } th[x] = acc; } }
    let lnpi = |s: usize| th[2 * s - 1] - th[s - 1]; // primes in [s,2s-1]
    let mut mid = 0f64; let mut mid_to_2000 = 0f64;
    for s in 41..=20000usize { let t = (-lnpi(s)).exp(); mid += t; if s <= 2000 { mid_to_2000 += t; } }
    println!("MID sum_{{41..2000}} 1/Pi_s = {:.6e} ; sum_{{41..20000}} = {:.6e}", mid_to_2000, mid);
    // Lemma 3b: ln L(s) = (s/3) ln4 - ln(2s+1) - sqrt(2s) ln(2s)
    let mut viol3b = vec![]; let mut min_margin = 1e18f64;
    for s in 2..=20000usize { let l = (s as f64 / 3.0) * 4f64.ln() - ((2 * s + 1) as f64).ln() - ((2 * s) as f64).sqrt() * ((2 * s) as f64).ln(); let m = lnpi(s) - l; if m < 0.0 { viol3b.push(s); } if s >= 3 && m < min_margin { min_margin = m; } }
    println!("Lemma 3b (Pi_s >= L(s)) violations for s in 2..20000: {:?} ; min ln-margin (s>=3) = {:.4}", viol3b, min_margin);
    let mut v4 = vec![]; for s in 2000..=20000usize { if lnpi(s) < (s as f64 / 4.0) * 2f64.ln() { v4.push(s); } }
    println!("Lemma 4 (Pi_s >= 2^(s/4)) violations 2000..20000: {:?} ; also smallest s>=2 for which Pi_s>=2^(s/4) holds for all larger s up to 20000:", v4);
    let mut last_bad = 0; for s in 2..=20000usize { if lnpi(s) < (s as f64 / 4.0) * 2f64.ln() { last_bad = s; } } println!("   last s<=20000 violating 2^(s/4): {}", last_bad);
    // tail s>2000 bound used
    let tail = 2f64.powf(-2001.0 / 4.0) / (1.0 - 2f64.powf(-0.25));
    println!("TAIL bound sum_{{s>=2001}} 2^(-s/4) = {:.3e}", tail);
    let total = dsum + mid_to_2000 + tail;
    println!("UPPER density of exceptional set <= {:.12} ; lower density of Y >= {:.12}", total, 1.0 - total);
    println!("claimed lb 985435322720210970443018065954/2^100 = {:.12}", 985435322720210970443018065954f64 / 2f64.powi(100));
    // sanity on d_s: monotone-ish list
    let mut s_ = String::new(); for s in 2..=14 { s_ += &format!("{}:{:.4e} ", s, dvals[s]); } println!("d_s: {}", s_);
    // sanity: Pi_s divides r bound: d_s <= 1/Pi_s ? (Lemma 2 consequence: d_s <= 1/Pi_s)
    let mut bad = vec![]; for s in 2..=40usize { if dvals[s] > (-lnpi(s)).exp() * (1.0 + 1e-9) { bad.push(s); } }
    println!("d_s <= 1/Pi_s violations (s=2..40): {:?}", bad);
}
