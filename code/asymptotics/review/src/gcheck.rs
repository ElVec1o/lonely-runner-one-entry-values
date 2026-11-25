// Fresh-session review check. Literal definition of G(N): all columns r in (N/2,N], no pruning.
// s=N+1-r; beta = least b>=s with gcd(b,r)=1 (linear scan); m = floor(beta/s)+1; V=m/(m r+beta); G=min V (exact, u64 cross-mult).
use std::io::Write;
use std::fs;
fn gcd(mut a: u32, mut b: u32) -> u32 { while b != 0 { let t = a % b; a = b; b = t; } a }
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut d = 2; while d * d <= n { if n % d == 0 { return false; } d += 1; } true }
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args[1].as_str();
    let dir = args[2].as_str();
    let nmax: u64 = args[3].parse().unwrap();
    let chunk: u64 = 5000;
    if mode == "run" {
        let mut lo = 2u64;
        while lo <= nmax {
            let hi = std::cmp::min(lo + chunk - 1, nmax);
            let fin = format!("{}/c_{:07}.tsv", dir, lo);
            if std::path::Path::new(&fin).exists() { lo = hi + 1; continue; }
            let tmp = format!("{}.tmp", fin);
            let mut out = std::io::BufWriter::new(fs::File::create(&tmp).unwrap());
            for n in lo..=hi {
                let a = n + 1;
                let mut bn: u64 = 0; let mut bd: u64 = 1; let mut br = 0u64;
                let mut anyforce = false; let mut mism = 0u32;
                let mods = [(2u64, 6u64), (3, 30), (4, 70), (5, 210)];
                let mut flag = [false; 6];
                let rmin = n / 2 + 1;
                for r in rmin..=n {
                    let s = a - r;
                    let mut b = s as u32;
                    while gcd(b, r as u32) != 1 { b += 1; }
                    let beta = b as u64;
                    let m = beta / s + 1;
                    let den = m * r + beta;
                    // identity check: den == m*A - e with e = m*s - beta in [1,s]
                    let e = m * s - beta;
                    assert!(e >= 1 && e <= s && den == m * a - e, "identity fail N={} r={}", n, r);
                    if s >= 2 && beta >= 2 * s { anyforce = true; if s <= 5 { flag[s as usize] = true; } }
                    if bn == 0 || m * bd < bn * den { bn = m; bd = den; br = r; }
                }
                for &(s, md) in mods.iter() {
                    if n + 2 >= 2 * s + 1 - 0 && n >= 2 * s - 1 { // r=N+1-s > N/2  <=> N >= 2s-1
                        let pred = (n + 1 - s) % md == 0;
                        if pred != flag[s as usize] { mism += 1; }
                    }
                }
                writeln!(out, "{}\t{}\t{}\t{}\t{}\t{}", n, bn, bd, br, anyforce as u8, mism).unwrap();
            }
            out.flush().unwrap(); drop(out);
            fs::rename(&tmp, &fin).unwrap();
            eprintln!("chunk {}..{} done", lo, hi);
            lo = hi + 1;
        }
        println!("RUN DONE");
    } else {
        // agg: read all chunks, recompute claims from stored fraction G=p/q
        let mut files: Vec<_> = fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().map_or(false, |x| x == "tsv")).collect();
        files.sort();
        let (mut cnt, mut strict, mut forced, mut forced_not_strict, mut strict_not_forced, mut mism) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let mut maxv = 0f64; let mut maxn = 0u64; let mut viol = 0u64;
        let mut minl = 1e9f64; let mut minln = 0u64;
        let mut primeA_fail = 0u64; let mut mod6_fail = 0u64; let mut mod6_n = 0u64; let mut primeA_n = 0u64;
        let mut prev = 1u64;
        let mut blockmax = vec![(0f64,0u64);40];
        for f in files {
            let t = fs::read_to_string(&f).unwrap();
            for line in t.lines() {
                let v: Vec<u64> = line.split('\t').map(|x| x.parse().unwrap()).collect();
                let (n, p, q, af, mm) = (v[0], v[1], v[2], v[4] != 0, v[5]);
                assert!(n == prev + 1, "gap in N at {}", n); prev = n;
                let a = n + 1;
                cnt += 1; mism += mm;
                // G = p/q ; strict iff p*(2N+1) < 2*q
                let st = (p as u128) * ((2 * n + 1) as u128) < 2 * (q as u128);
                let eq = (p as u128) * ((2 * n + 1) as u128) == 2 * (q as u128);
                assert!(st || eq, "G above 2/(2N+1) at N={}", n);
                if st { strict += 1; }
                if af { forced += 1; }
                if af && !st { forced_not_strict += 1; }
                if st && !af { strict_not_forced += 1; }
                // N^2 (G-1/A) < 1/2 exact:  N^2*(p*A-q)*2 < q*A
                let num = (p as i128) * (a as i128) - (q as i128); // = p*A - q, G-1/A = num/(q*A)
                assert!(num > 0);
                let lhs = (n as i128) * (n as i128) * num * 2; let rhs = (q as i128) * (a as i128);
                if !(lhs < rhs) { viol += 1; }
                let val = (n as f64) * (n as f64) * (num as f64) / ((q as f64) * (a as f64));
                if val > maxv { maxv = val; maxn = n; }
                let k = (63 - n.leading_zeros()) as usize;
                if val > blockmax[k].0 { blockmax[k] = (val, n); }
                if n >= 8 { let l = (n as f64).ln() * val; if l < minl { minl = l; minln = n; } }
                if is_prime(a) { primeA_n += 1; if !eq { primeA_fail += 1; } }
                if n >= 7 && n % 6 == 1 { mod6_n += 1; if !st { mod6_fail += 1; } }
            }
        }
        println!("N=2..{} count={} strict={} (density {:.6}) equal={} (density {:.6})", prev, cnt, strict, strict as f64 / cnt as f64, cnt - strict, (cnt - strict) as f64 / cnt as f64);
        println!("any-forcing(s>=2, some column beta>=2s)={} ; forced_not_strict={} ; strict_not_forced={}", forced, forced_not_strict, strict_not_forced);
        println!("congruence mismatches (s=2..5, vs 6/30/70/210) = {}", mism);
        println!("N^2(G-1/A)<1/2 violations = {} ; max N^2(G-1/A) = {:.9} at N={}", viol, maxv, maxn);
        println!("A prime: {} cases, G!=2/(2N+1) in {} ; N=1 mod 6,N>=7: {} cases, not strict in {}", primeA_n, primeA_fail, mod6_n, mod6_fail);
        println!("min over N>=8 of logN*N^2(G-1/A) = {:.6} at N={}", minl, minln);
        for k in 3..40 { if blockmax[k].1 != 0 { println!("dyadic block 2^{}: max N^2(G-1/A)={:.9} at N={}", k, blockmax[k].0, blockmax[k].1); } }
    }
}
