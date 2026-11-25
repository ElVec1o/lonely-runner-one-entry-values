// dens_cert.rs (the accompanying code, 2026-11-24, DRAFT): exact-integer verifier for the lower-density bound of
// {N : G(N) = 2/(2N+1)}.  See the accompanying notes.  No floating point enters any inequality that is asserted;
// f64 appears only in printed decimals and in the sanity checks marked (f64-sanity).
//   Stage A  exact d_s = num_s/den_s for s=2..=SE=40 by subset enumeration over the primes < 2s (u128), with
//            upper bounds in units of 2^-100 (exact long division, rounded up).
//   Stage B  independent check of num_s by direct enumeration of ALL residues mod den_s (s<=14).
//   Stage C  Pi_s = prod_{s<=p<=2s-1} p as a big integer (incremental), exact bit length; tail
//            sum_{s=SE+1..S0} 1/Pi_s <= sum 2^{-(bitlen-1)} in units 2^-100 (rounded up).
//            Controls: incremental vs from-scratch product; vs u128 for s<=60.
//   Stage D  analytic tail s>S0=2000 (Pi_s >= 2^{s/4}); the numeric premise k(S0)>0, k'(S0)>0 is evaluated here.
//   Stage E  brute force over N<=10^6 per s (genuine definition of forcing), exact equality when den_s | range.
//   Stage F  Lemma 0 against the literal definition of G(N) (all r, N<=20000): not forced => G = 2/(2N+1).
// Output: final rigorous lower bound as an integer fraction over 2^100.
use std::time::Instant;

fn gcd(a: u64, b: u64) -> u64 { let (mut a, mut b) = (a, b); while b != 0 { let t = a % b; a = b; b = t; } a }

fn sieve(n: usize) -> Vec<bool> {
    let mut c = vec![true; n + 1]; c[0] = false; if n >= 1 { c[1] = false; }
    let mut i = 2; while i * i <= n { if c[i] { let mut j = i * i; while j <= n { c[j] = false; j += i; } } i += 1; }
    c
}

fn ub_units(num: u128, den: u128) -> u128 { // ceil(num/den * 2^100); requires den < 2^126
    let mut rem = num; let mut out: u128 = 0;
    for _ in 0..100 { rem *= 2; out <<= 1; if rem >= den { rem -= den; out |= 1; } }
    if rem > 0 { out += 1; }
    out
}

fn mul_small(v: &mut Vec<u32>, m: u32) { let mut c: u64 = 0; for x in v.iter_mut() { let t = (*x as u64) * (m as u64) + c; *x = t as u32; c = t >> 32; } if c > 0 { v.push(c as u32); } }
fn div_small(v: &mut Vec<u32>, d: u32) {
    let mut rem: u64 = 0;
    for x in v.iter_mut().rev() { let t = (rem << 32) | (*x as u64); *x = (t / d as u64) as u32; rem = t % d as u64; }
    assert_eq!(rem, 0, "inexact division");
    while v.len() > 1 && *v.last().unwrap() == 0 { v.pop(); }
}
fn bitlen(v: &Vec<u32>) -> usize { 32 * (v.len() - 1) + (32 - v.last().unwrap().leading_zeros() as usize) }
fn pi_direct(s: usize, isp: &Vec<bool>) -> Vec<u32> {
    let mut v = vec![1u32]; for p in s..=(2 * s - 1) { if isp[p] { mul_small(&mut v, p as u32); } } v
}

fn main() {
    let t0 = Instant::now();
    const SE: usize = 40; const S0: usize = 2000; const S1: usize = 20000;
    let isp = sieve(2 * S1 + 10);
    let one: u128 = 1u128 << 100;

    // ---------------- Stage A
    let mut nums: Vec<(u128, u128)> = vec![(0, 1); SE + 1];
    let mut sum_a: u128 = 0;
    for s in 2..=SE {
        let pr: Vec<u64> = (2..2 * s as u64).filter(|&p| isp[p as usize]).collect(); let k = pr.len();
        let masks: Vec<u32> = (s..2 * s).map(|b| { let mut m = 0u32; for (i, &p) in pr.iter().enumerate() { if (b as u64) % p == 0 { m |= 1 << i; } } m }).collect();
        let mut den: u128 = 1; for &p in &pr { den = den.checked_mul(p as u128).expect("den overflow"); }
        let mut num: u128 = 0;
        for q in 0u32..(1u32 << k) {
            if masks.iter().all(|&m| m & q != 0) {
                let mut w: u128 = 1; for i in 0..k { if (q >> i) & 1 == 0 { w = w.checked_mul((pr[i] - 1) as u128).expect("w overflow"); } }
                num = num.checked_add(w).expect("num overflow");
            }
        }
        assert!(num <= den);
        let g = { let (mut a, mut b) = (num, den); while b != 0 { let t = a % b; a = b; b = t; } a };
        let ub = ub_units(num, den); sum_a += ub; nums[s] = (num, den);
        println!("A s={:>2} k={:>2} num={} den={} d_s={}/{} = {:.8e}  ub_units={}", s, k, num, den, num / g, den / g, num as f64 / den as f64, ub);
    }
    println!("A SUM_{{s=2..{}}} d_s upper units(2^-100) = {}  ~ {:.12}", SE, sum_a, sum_a as f64 / one as f64);
    // closed forms for control: d_2=1/6, d_3=1/30, d_4=1/70, d_5=1/210, d_6=1/462, d_7=1/6006, d_8=1/858
    for (s, d) in [(2usize, 6u128), (3, 30), (4, 70), (5, 210), (6, 462), (7, 6006), (8, 858)] {
        let (n, dn) = nums[s]; assert!(n * d == dn, "closed form mismatch s={}", s);
    }
    println!("A closed-form controls d_2..d_8 OK ({:.1}s)", t0.elapsed().as_secs_f64());

    // ---------------- Stage B: independent full-period enumeration
    for s in 2..=14usize {
        let pr: Vec<u64> = (2..2 * s as u64).filter(|&p| isp[p as usize]).collect();
        let den: u64 = pr.iter().product();
        let mut cnt: u128 = 0;
        for r in 0..den { let mut ok = true; for b in s as u64..2 * s as u64 { if gcd(b, r) == 1 { ok = false; break; } } if ok { cnt += 1; } }
        assert_eq!(den as u128, nums[s].1); assert_eq!(cnt, nums[s].0, "stage B mismatch s={}", s);
        println!("B s={:>2} period {} count {} == num_s  OK ({:.1}s)", s, den, cnt, t0.elapsed().as_secs_f64());
    }

    // ---------------- Stage C: big-integer Pi_s
    let mut v = pi_direct(SE + 1, &isp);
    let mut sum_c: u128 = 0; let mut sum_c_exact_leq100 = 0u32;
    let mut min_margin = f64::MAX;
    for s in (SE + 1)..=S1 {
        if s > SE + 1 { // step from s-1 to s : remove p=s-1 if prime, add p=2s-3? -- done below via explicit update
        }
        let bl = bitlen(&v);
        if s <= S0 { let e = bl - 1; sum_c += if e <= 100 { sum_c_exact_leq100 += 1; 1u128 << (100 - e) } else { 1 }; }
        // (f64-sanity) Erdos lower bound: log2 L(s) <= bitlen(Pi_s)
        let sf = s as f64; let lg = 2.0 * sf / 3.0 - (2.0 * sf + 1.0).log2() - (2.0 * sf).sqrt() * (2.0 * sf).log2();
        assert!(lg < bl as f64, "Erdos lower bound violated at s={}", s);
        if s >= S0 { assert!(bl - 1 >= s / 4, "Pi_s >= 2^(s/4) fails at s={}", s); let m = (bl - 1) as f64 - sf / 4.0; if m < min_margin { min_margin = m; } }
        if s <= 60 { let mut u: u128 = 1; for p in s..=(2 * s - 1) { if isp[p] { u = u.checked_mul(p as u128).unwrap(); } }
            let mut w = vec![1u32]; let mut t = u; let mut limbs = vec![]; while t > 0 { limbs.push((t & 0xffff_ffff) as u32); t >>= 32; } if limbs.is_empty() { limbs.push(1); } w = limbs; assert_eq!(w, v, "u128 control mismatch s={}", s); }
        if [41usize, 100, 500, 1000, 2000, 5000, 12345, 20000].contains(&s) { assert_eq!(pi_direct(s, &isp), v, "incremental != from scratch at s={}", s); println!("C control s={} bits(Pi_s)={} incremental==direct OK", s, bl); }
        // advance s -> s+1: Pi_{s+1} = Pi_s / s (if s prime) * (2s+1 if prime)   [2s is even >= 4 here]
        if isp[s] { div_small(&mut v, s as u32); }
        if isp[2 * s + 1] { mul_small(&mut v, (2 * s + 1) as u32); }
    }
    println!("C SUM_{{s={}..{}}} 1/Pi_s <= sum 2^-(bitlen-1): units(2^-100) = {}  ~ {:.6e}  (terms with exponent<=100: {})", SE + 1, S0, sum_c, sum_c as f64 / one as f64, sum_c_exact_leq100);
    println!("C min over s in [{},{}] of (bitlen-1 - s/4) = {:.3}  (must be >= 0)  ({:.1}s)", S0, S1, min_margin, t0.elapsed().as_secs_f64());

    // ---------------- Stage D: analytic tail premise  k(s) = (5/12) s - log2(2s+1) - sqrt(2s) log2(2s) >= 0 for s>=S0
    let sf = S0 as f64; let kk = 5.0 / 12.0 * sf - (2.0 * sf + 1.0).log2() - (2.0 * sf).sqrt() * (2.0 * sf).log2();
    let lnt = (2.0 * sf).ln(); let kp = 5.0 / 12.0 - 2.0 / ((2.0 * sf + 1.0) * std::f64::consts::LN_2) - (lnt + 2.0) / ((2.0 * sf).sqrt() * std::f64::consts::LN_2);
    println!("D k({})={:.4}  k'({})={:.5}  (both must be > 0; (f64-sanity), margins are large)", S0, kk, S0, kp);
    assert!(kk > 10.0 && kp > 0.1);
    // tail sum_{s>S0} 2^{-s/4} = 2^{-(S0+1)/4}/(1-2^{-1/4}) < 2^{-498} < 1 unit.
    let sum_d: u128 = 1;

    // ---------------- Final
    let total = sum_a + sum_c + sum_d;
    let lb = one - total;
    println!("FINAL upper bound on upper density of {{N: G(N)<2/(2N+1)}} <= total/2^100, total = {}  ~ {:.12}", total, total as f64 / one as f64);
    println!("FINAL lower density of {{N: G(N)=2/(2N+1)}} >= {}/2^100 ~ {:.12}", lb, lb as f64 / one as f64);
    assert!(lb * 10000 >= 7773 * one, "0.7773 not reached");
    assert!(lb * 100000 >= 77737 * one, "0.77737 not reached");
    println!("FINAL assert: lower density >= 0.77737 holds in exact integer arithmetic ({:.1}s)", t0.elapsed().as_secs_f64());

    // ---------------- Stage E: brute force N<=10^6 per s (unrestricted E'_s: r=N+1-s>=1; all b in [s,2s-1] have gcd(b,r)>1)
    let x: u64 = 1_000_000;
    for s in 2..=14u64 {
        let mut cnt: u64 = 0;
        for n in s..=x { let r = n + 1 - s; let mut ok = true; for b in s..2 * s { if gcd(b, r) == 1 { ok = false; break; } } if ok { cnt += 1; } }
        let (num, den) = nums[s as usize];
        let pred = x as f64 * num as f64 / den as f64;
        // exact equality over r in [1, R], R = floor(x'/den)*den, x' = x+1-s : each residue class appears exactly R/den times
        let xp = x + 1 - s; let mut exact = String::from("n/a (period > range)");
        if den <= xp as u128 { let rr = (xp as u128 / den) * den; let mut c2: u128 = 0; for r in 1..=rr as u64 { let mut ok = true; for b in s..2 * s { if gcd(b, r) == 1 { ok = false; break; } } if ok { c2 += 1; } }
            assert_eq!(c2, rr / den * num, "stage E exactness fails s={}", s); exact = format!("exact over r<={}: {} == {}", rr, c2, rr / den * num); }
        println!("E s={:>2} brute count N<=10^6: {}  predicted d_s*x = {:.2}  {}", s, cnt, pred, exact);
    }
    // union over s of the GENUINE forcing sets (r=N+1-s with N<2r, i.e. N>=2s-1), s up to 60
    let mut uni = 0u64; let mut bys = [0u64; 61];
    for n in 2..=x { let mut any = false; for s in 2..=60u64 { if n < 2 * s - 1 { break; } let r = n + 1 - s; let mut ok = true; for b in s..2 * s { if gcd(b, r) == 1 { ok = false; break; } } if ok { any = true; bys[s as usize] += 1; } } if any { uni += 1; } }
    println!("E union of genuine forcing sets s=2..60, N=2..10^6: {} ({:.5}); bound sum d_s = {:.5}", uni, uni as f64 / x as f64, sum_a as f64 / one as f64);

    // ---------------- Stage F: Lemma 0 against the literal definition of G(N)
    let nf: u64 = 20000; let (mut strict, mut forced, mut forced_not_strict) = (0u64, 0u64, 0u64);
    for n in 2..=nf {
        let a = n + 1; let mut strict_n = false; // exists r with V_r < 2/(2N+1)
        for r in (n / 2 + 1)..=n { // N < 2r
            if !(n < 2 * r) { continue; }
            let s = a - r; let mut b = s; while gcd(b, r) != 1 { b += 1; }
            let m = b / s + 1; // V_r = m/(m r + b); V_r < 2/(2N+1)  <=>  m(2N+1) < 2(m r + b)
            if m * (2 * n + 1) < 2 * (m * r + b) { strict_n = true; }
            if m == 2 { assert!(m * (2 * n + 1) >= 2 * (m * r + b) || false, "m=2 gave V_r < 2/(2N+1) at N={} r={}", n, r); }
        }
        let mut f = false;
        for s in 2..=n { if n < 2 * s - 1 { break; } let r = a - s; let mut ok = true; for b in s..2 * s { if gcd(b, r) == 1 { ok = false; break; } } if ok { f = true; break; } }
        if strict_n { strict += 1; assert!(f, "LEMMA 0 FAILS: G<2/(2N+1) but no forcing s at N={}", n); }
        if f { forced += 1; if !strict_n { forced_not_strict += 1; } }
    }
    println!("F N=2..{}: strict {} (all forced: Lemma 0 holds), forced {}, forced-not-strict {}  ({:.1}s)", nf, strict, forced, forced_not_strict, t0.elapsed().as_secs_f64());
    println!("DONE");
}
