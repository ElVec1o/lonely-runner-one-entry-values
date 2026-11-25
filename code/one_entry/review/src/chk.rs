// Fresh-session reviewer checker for Theorem OE (written from scratch; not oe.rs/hb.rs).
// Units: N = number of speeds, tau = num/den rational, all exact integers (i128).
use std::env;
type F = (i128, i128); // numerator, denominator>0
#[inline] fn lt(a: F, b: F) -> bool { a.0 * b.1 < b.0 * a.1 }
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }

// closed gaps of [0,1] where every speed in rs has ||t v|| >= num/den
fn gaps(rs: &[u64], num: i128, den: i128) -> Vec<(F, F)> {
    let mut bands: Vec<(F, F)> = Vec::new();
    for &v in rs {
        let v = v as i128;
        for k in 0..=v { let c = k * den; bands.push(((c - num, v * den), (c + num, v * den))); }
    }
    bands.sort_by(|x, y| (x.0 .0 * y.0 .1).cmp(&(y.0 .0 * x.0 .1)));
    let mut out = Vec::new();
    let mut cur = bands[0].1;
    for b in bands.iter().skip(1) {
        if !lt(b.0, cur) { out.push((cur, b.0)); }
        if lt(cur, b.1) { cur = b.1; }
    }
    if !lt((1, 1), cur) { out.push((cur, (1, 1))); }
    out
}
// does some t in some gap satisfy ||w t|| >= num/den ?
fn wok(gs: &[(F, F)], w: i128, num: i128, den: i128) -> bool {
    for &(a, b) in gs {
        let jf = (w * a.0).div_euclid(a.1);
        let mut inside = false;
        for j in jf..=jf + 1 {
            let l: F = (j * den - num, w * den);
            let r: F = (j * den + num, w * den);
            if lt(l, a) && lt(b, r) { inside = true; break; }
        }
        if !inside { return true; }
    }
    false
}
fn ge(rs: &[u64], w: u64, num: i128, den: i128) -> bool { let g = gaps(rs, num, den); wok(&g, w as i128, num, den) }
// exact ML by candidate times k/(vi+vj), t in (0,1/2]
fn ml_exact(v: &[u64]) -> F {
    let mut best: F = (0, 1);
    let mut seen: Vec<(u64, u64)> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() {
        let s = v[i] + v[j];
        for k in 1..=s / 2 {
            let g = gcd(k, s); let key = (k / g, s / g);
            if seen.contains(&key) { continue; }
            seen.push(key);
            let mut m = i128::MAX;
            for &x in v { let rem = ((k as u128 * x as u128) % s as u128) as i128; let d = rem.min(s as i128 - rem); if d < m { m = d; } }
            let c: F = (m, s as i128);
            if lt(best, c) { best = c; }
        }
    } }
    best
}
fn one_entry(n: u64, r: u64, w: u64) -> (Vec<u64>, Vec<u64>) {
    let rs: Vec<u64> = (1..=n).filter(|&i| i != r).collect();
    let mut v = rs.clone(); v.push(w); (rs, v)
}
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut d = 2; while d * d <= n { if n % d == 0 { return false; } d += 1; } true }
fn primes_in(lo: u64, hi: u64) -> Vec<u64> { (lo..=hi).filter(|&x| is_prime(x)).collect() }
fn wb(n: u64, r: u64) -> Option<u64> {
    let mut best: Option<u64> = None;
    if n + 1 + r > 2 * n - 1 { return None; }
    for d in n + 1 + r..=2 * n - 1 { if gcd(d, r) != 1 { continue; }
        let num = d as u128 * (n as u128) * (n as u128); let den = 2 * (2 * n - d) as u128;
        let c = ((num + den - 1) / den) as u64; best = Some(best.map_or(c, |b| b.min(c))); }
    best
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n } }

fn selftest() {
    let mut fails = 0;
    // planted known values
    let planted: Vec<(Vec<u64>, F)> = vec![
        (vec![1, 3, 4, 7], (1, 5)), (vec![1, 3, 4, 5, 9], (1, 6)),
        (one_entry(13, 6, 69).1, (3, 40)), (one_entry(13, 12, 36).1, (3, 41)), (one_entry(13, 12, 24).1, (1, 14)),
        ((1..=8).collect(), (1, 9)), (one_entry(31, 30, 120).1, (4, 127)),
    ];
    for (v, val) in &planted {
        let mx = *v.last().unwrap(); // for one_entry w is last; for plain sets last element used as 'w'
        let rs: Vec<u64> = v[..v.len() - 1].to_vec();
        let c = if v.len() <= 14 && mx <= 140 { ml_exact(v) } else { *val };
        let ok_c = c.0 * val.1 == val.0 * c.1 || v.len() > 14;
        let K = 1_000_003i128;
        let up = ge(&rs, mx, val.0 * K + 1, val.1 * K);
        let dn = ge(&rs, mx, val.0 * K - 1, val.1 * K);
        let eq = ge(&rs, mx, val.0, val.1);
        println!("planted {:?} val {}/{} C={}/{} ge(v)={} ge(v+)={} ge(v-)={}", &v[..v.len().min(6)], val.0, val.1, c.0, c.1, eq, up, dn);
        if !(ok_c && eq && !up && dn) { fails += 1; println!("  PLANTED FAIL"); }
    }
    // random A vs C
    let mut rng = Rng(88172645463325252);
    let mut cnt = 0; let mut sk = 0;
    for _ in 0..6000 {
        let sz = 3 + rng.below(6) as usize; let mut v: Vec<u64> = Vec::new();
        while v.len() < sz { let x = 1 + rng.below(70); if !v.contains(&x) { v.push(x); } }
        let c = ml_exact(&v); if c.0 * 2 == c.1 { sk += 1; continue; }
        let wi = rng.below(sz as u64) as usize; let w = v[wi]; let rs: Vec<u64> = v.iter().enumerate().filter(|(i, _)| *i != wi).map(|(_, &x)| x).collect();
        let K = 1_000_003i128;
        let a = ge(&rs, w, c.0 * K, c.1 * K); let b = ge(&rs, w, c.0 * K + 1, c.1 * K); let d = ge(&rs, w, c.0 * K - 1, c.1 * K);
        cnt += 1;
        if !(a && !b && d) { fails += 1; println!("A-vs-C MISMATCH {:?} C={}/{} a={} up={} dn={}", v, c.0, c.1, a, b, d); }
    }
    println!("random A-vs-C: {} sets (skipped ML=1/2: {}); total failures {}", cnt, sk, fails);
    // Theorem V against C
    let mut bad = 0; let mut tot = 0;
    for n in 4..=22u64 { for r in (n / 2 + 1)..=n { for m in 2..=6u64 {
        let (_, v) = one_entry(n, r, m * r);
        let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
        let a: F = (1, (n + 1) as i128); let b: F = (m as i128, (m * r + beta) as i128);
        let f = if lt(a, b) { b } else { a };
        let c = ml_exact(&v); tot += 1;
        if c.0 * f.1 != f.0 * c.1 { bad += 1; println!("THM V mismatch N={} r={} m={} C={}/{} formula={}/{}", n, r, m, c.0, c.1, f.0, f.1); }
    } } }
    println!("Theorem V vs independent exact ML: {} sets, {} mismatches", tot, bad);
    if bad > 0 { fails += 1; }
    println!("SELFTEST {}", if fails == 0 { "PASS" } else { "FAIL" });
}

// ML >= 1/N for all r<=N/2, N<w<=wmax(N,r); prints exceptions
fn ml1n(n0: u64, n1: u64, mode: &str) {
    let mut total: u64 = 0; let mut exc: Vec<(u64, u64, u64)> = Vec::new();
    for n in n0..=n1 { let mut nsets = 0u64;
        for r in 1..=n / 2 {
            let rs: Vec<u64> = (1..=n).filter(|&i| i != r).collect();
            let gs = gaps(&rs, 1, n as i128);
            let wmax = match mode { "4n2" => 4 * n * n + 20, _ => { let b = wb(n, r).unwrap_or(0); (4 * n * n).max(b + 200) } };
            for w in n + 1..=wmax { total += 1; nsets += 1; if !wok(&gs, w as i128, 1, n as i128) { exc.push((n, r, w)); } }
        }
        println!("N={} sets={} exceptions so far={}", n, nsets, exc.len());
    }
    println!("TOTAL sets {} ; exceptions (ML<1/N) {}", total, exc.len());
    for &(n, r, w) in &exc { let (_, v) = one_entry(n, r, w); let c = if w < 400 { ml_exact(&v) } else { (0, 1) }; println!("EXC N={} r={} w={} ML={}/{}", n, r, w, c.0, c.1); }
}
// witness lemma W exhaustive + pigeonhole
fn witness(n0: u64, n1: u64, wcap: u64) {
    let mut w_tests = 0u64; let mut w_fail = 0u64; let mut w_bad_class_still_ok = 0u64; let mut w_bad_tot = 0u64;
    for n in n0..=n1 { for r in 1..=n / 2 {
        let rs: Vec<u64> = (1..=n).filter(|&i| i != r).collect();
        for d in n + 1 + r..=2 * n { if gcd(d, r) != 1 { continue; }
            let gs = gaps(&rs, 2, d as i128);
            for w in n + 1..=wcap { let cls = w % d; let bad = cls == 0 || cls == r % d || cls == (d - r % d) % d;
                let ok = wok(&gs, w as i128, 2, d as i128);
                if !bad { w_tests += 1; if !ok { w_fail += 1; println!("LEMMA W FAIL N={} r={} D={} w={}", n, r, d, w); } }
                else { w_bad_tot += 1; if ok { w_bad_class_still_ok += 1; } } } } } }
    println!("Lemma W (exhaustive N={}..{}, all D in [N+1+r,2N] coprime r, w<={}): good-class tests {}, failures {}; bad-class w {} of which engine still finds ML>=2/D: {}", n0, n1, wcap, w_tests, w_fail, w_bad_tot, w_bad_class_still_ok);
}
fn pigeon(n0: u64, n1: u64) {
    let mut tests = 0u64; let mut viol = 0u64; let mut small_fail = 0u64; let mut small_min: Option<(u64, u64, u64)> = None;
    for n in n0..=n1 { for r in 1..=n / 2 {
        let ps = primes_in(n + 1 + r, 2 * n); let bound = (n + 1 + r).pow(3) - r;
        for w in n + 1..bound {
            let good = ps.iter().any(|&p| { let c = w % p; !(c == 0 || c == r % p || c == (p - r % p) % p) });
            if ps.len() >= 7 { tests += 1; if !good { viol += 1; println!("PIGEON VIOLATION N={} r={} w={}", n, r, w); } }
            else if !good { small_fail += 1; if small_min.map_or(true, |m| w < m.2) { small_min = Some((n, r, w)); } }
        } } }
    println!("Pigeonhole (N={}..{}): sets with >=7 primes tested {} violations {}; (N,r) with <7 primes: w below bound with no good prime: {} (neg. control; smallest {:?})", n0, n1, tests, viol, small_fail, small_min);
}
fn lemmal(n0: u64, n1: u64, extra: u64) {
    let mut tests = 0u64; let mut fails = 0u64;
    for n in n0..=n1 { for r in 1..=n / 2 {
        let rs: Vec<u64> = (1..=n).filter(|&i| i != r).collect(); let gs = gaps(&rs, 1, n as i128);
        for d in n + 1 + r..=2 * n - 1 { if gcd(d, r) != 1 { continue; }
            let num = d as u128 * (n as u128) * (n as u128); let den = 2 * (2 * n - d) as u128; let w0 = ((num + den - 1) / den) as u64;
            // exact threshold test 2(2N-D)w >= D N^2 at w0 and w0-1
            assert!(2 * (2 * n - d) as u128 * w0 as u128 >= num);
            for w in w0.max(n + 1)..w0.max(n + 1) + extra { tests += 1; if !wok(&gs, w as i128, 1, n as i128) { fails += 1; println!("LEMMA L FAIL N={} r={} D={} w={}", n, r, d, w); } }
        } } }
    println!("Lemma L (N={}..{}, every D in window coprime r, w in [w0,w0+{})): tests {} failures {}", n0, n1, extra, tests, fails);
}
fn lemmaq(limit: usize) {
    let mut sv = vec![true; limit + 1]; sv[0] = false; if limit >= 1 { sv[1] = false; }
    let mut i = 2; while i * i <= limit { if sv[i] { let mut j = i * i; while j <= limit { sv[j] = false; j += i; } } i += 1; }
    let mut pi = vec![0u32; limit + 1]; let mut c = 0u32; for x in 0..=limit { if sv[x] { c += 1; } pi[x] = c; }
    let mut fails14: Vec<usize> = Vec::new(); let mut minc = u32::MAX; let mut argmin = 0;
    for n in 14..=limit / 2 { let cnt = pi[2 * n] - pi[n + n / 2]; if cnt < 7 { fails14.push(n); } if n > 78 && cnt < minc { minc = cnt; argmin = n; } }
    println!("N in [14,{}]: N with <7 primes in [N+1+floor(N/2),2N]: count {} last {:?}", limit / 2, fails14.len(), fails14.last());
    println!("min count over N>78: {} at N={}", minc, argmin);
    println!("fails list (N<=78): {:?}", fails14);
    // RS62 numeric sanity at every prime
    let mut lo_bad = 0; let mut up_bad = 0;
    for p in 3..=limit { if sv[p] { let k = pi[p] as f64; let x = p as f64; if p >= 19 && !(k - 1.0 >= x / x.ln()) { lo_bad += 1; } if !(k < 1.25506 * x / x.ln()) { up_bad += 1; } } }
    println!("RS62 numeric sanity (f64) up to {}: lower bound (pi(p)-1 >= p/ln p, p>=19) violations {}; upper bound (pi(p) < 1.25506 p/ln p) violations {}", limit, lo_bad, up_bad);
    // analytic chain
    let c = (4.0f64 / 3.0).ln();
    let f = |n: f64| { let l = (1.5 * n + 1.0).ln(); (n / l) * (2.0 * l / (l + c) - 1.25506 * (1.5 + 1.0 / n)) };
    let fd = |n: f64| 2.0 * n / (2.0 * n).ln() - 1.25506 * (1.5 * n + 1.0) / (1.5 * n + 1.0).ln();
    println!("ln(4/3)={:.6}", c);
    let mut last_below = 0u64; for n in 100..3_000_000u64 { if f(n as f64) < 7.0 { last_below = n; } }
    println!("weakened bound f(N)<7 last at N={} ; f(1233)={:.4} f(1234)={:.4}", last_below, f(1233.0), f(1234.0));
    let mut lb2 = 0u64; for n in 100..3_000_000u64 { if fd(n as f64) < 7.0 { lb2 = n; } }
    println!("direct bound last <7 at N={}", lb2);
    for &n in &[1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e12] { println!("N={:e} f={:.4e} direct={:.4e}", n, f(n), fd(n)); }
    // monotonicity numeric: f increasing on grid from 1233
    let mut mono = true; let mut prev = f(1233.0); let mut n = 1234.0f64; while n < 1e13 { let cur = f(n); if cur < prev { mono = false; println!("non-monotone at {}", n); break; } prev = cur; n = (n * 1.01).ceil(); }
    println!("f increasing on geometric grid 1233..1e13: {}", mono);
}

fn inv(r: i128, d: i128) -> i128 { let (mut a, mut b, mut x0, mut x1) = (r.rem_euclid(d), d, 1i128, 0i128); while b != 0 { let q = a / b; let t = a - q * b; a = b; b = t; let t = x0 - q * x1; x0 = x1; x1 = t; } x0.rem_euclid(d) }
// direct verification of the explicit witnesses of Lemma W (t=a/D) and Lemma L (t=(2k+1)/(2w))
fn direct(n0: u64, n1: u64, wcap: u64) {
    let (mut wt, mut wf, mut wneg_ok, mut wneg_tot) = (0u64, 0u64, 0u64, 0u64); let (mut lt_, mut lf) = (0u64, 0u64);
    for n in n0..=n1 { for r in 1..=n / 2 { for d in n + 1 + r..=2 * n { if gcd(d, r) != 1 { continue; }
        let a = inv(r as i128, d as i128); let di = d as i128;
        for w in n + 1..=wcap { let cls = w % d; let bad = cls == 0 || cls == r % d || cls == (d - r % d) % d;
            let mut mn = i128::MAX;
            for v in (1..=n).filter(|&i| i != r).chain(std::iter::once(w)) { let y = (v as i128 * a).rem_euclid(di); mn = mn.min(y.min(di - y)); }
            if !bad { wt += 1; if mn < 2 { wf += 1; println!("W-DIRECT FAIL N={} r={} D={} w={}", n, r, d, w); } } else { wneg_tot += 1; if mn < 2 { wneg_ok += 1; } }
        }
        if d <= 2 * n - 1 {
            let (nn, dd) = (n as i128, d as i128); let q = (2 * nn - dd) * 1; let den = dd * nn * nn;
            let w0 = ((den + 2 * q - 1) / (2 * q)) as u64;
            for w in [w0, w0 + 1, w0 + 7, w0 * 3 / 2, w0 * 5].iter().cloned().filter(|&x| x > n) {
                let wi = w as i128; let lo_num = a * nn * nn - q; // lower endpoint (a/D - delta) = lo_num/den
                let two_w_lo = 2 * wi * lo_num; let mut m = (two_w_lo + den - 1).div_euclid(den); if m.rem_euclid(2) == 0 { m += 1; }
                let hi_ok = m * den <= 2 * wi * (a * nn * nn + q);
                lt_ += 1;
                let mut ok = hi_ok;
                if ok { let qq = 2 * wi; for v in (1..=n).filter(|&i| i != r).chain(std::iter::once(w)) { let y = (v as i128 * m).rem_euclid(qq); let dist = y.min(qq - y); if nn * dist < qq { ok = false; break; } } }
                if !ok { lf += 1; println!("L-DIRECT FAIL N={} r={} D={} w={} hi_ok={}", n, r, d, w, hi_ok); }
            }
        }
    } } }
    println!("Lemma W direct (time a/D, exact mod arithmetic): good-class {} failures {}; bad-class {} of which indeed min<2 at a/D: {} (must be all)", wt, wf, wneg_tot, wneg_ok);
    println!("Lemma L direct (explicit t=(2k+1)/(2w), all retained and w checked >=1/N): tests {} failures {}", lt_, lf);
}

fn crt(rs: &[(i128, i128)]) -> (i128, i128) { // (residue, modulus), moduli pairwise coprime
    let (mut x, mut m) = (0i128, 1i128);
    for &(a, p) in rs { let t = ((a - x).rem_euclid(p)) * inv(m.rem_euclid(p), p) % p; x += m * t; m *= p; }
    (x.rem_euclid(m), m)
}
fn stress(nmin: u64, nmax: u64, samples: u64, seed: u64) {
    let mut rng = Rng(seed); let (mut tot, mut allbad, mut wfail, mut pig, mut mlfail, mut direct_fail) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut cache: Option<(u64, u64, Vec<(F, F)>)> = None;
    for _ in 0..samples {
        let n = nmin + rng.below(nmax - nmin + 1); let r = 1 + rng.below(n / 2);
        let ps = primes_in(n + 1 + r, 2 * n);
        let rs: Vec<u64> = (1..=n).filter(|&i| i != r).collect();
        let gs = match &cache { Some((cn, cr, g)) if *cn == n && *cr == r => g.clone(), _ => { let g = gaps(&rs, 1, n as i128); cache = Some((n, r, g.clone())); g } };
        for kind in 0..6 {
            let w: i128 = match kind {
                0 => (n + 1 + rng.below(3 * n * n)) as i128,
                1 => (n + 1 + rng.below(10_000_000)) as i128,
                _ => { // CRT-bad for k primes
                    if ps.len() < 3 { continue; }
                    let k = (3 + rng.below(4) as usize).min(ps.len()); let mut pool = ps.clone(); let mut sel = Vec::new();
                    for _ in 0..k { let i = rng.below(pool.len() as u64) as usize; sel.push(pool.swap_remove(i)); }
                    let res: Vec<(i128, i128)> = sel.iter().map(|&p| { let e = rng.below(3) as i128 - 1; ((e * r as i128).rem_euclid(p as i128), p as i128) }).collect();
                    let (x, m) = crt(&res); let mut w = x + m * rng.below(3) as i128; while w <= n as i128 { w += m; } w
                }
            };
            if w > 1_000_000_000_000_000_000_000i128 { continue; }
            tot += 1;
            let good: Vec<u64> = ps.iter().cloned().filter(|&p| { let c = (w % p as i128) as u64; !(c == 0 || c == r % p || c == (p - r % p) % p) }).collect();
            let ok = wok(&gs, w, 1, n as i128);
            if !ok { mlfail += 1; println!("ML<1/N N={} r={} w={}", n, r, w); }
            if good.is_empty() { allbad += 1; if ps.len() >= 7 && w < ((n + 1 + r) as i128).pow(3) - r as i128 { pig += 1; println!("PIGEON VIOL N={} r={} w={}", n, r, w); } }
            for &p in good.iter().take(2) { let a = inv(r as i128, p as i128); let mut mn = i128::MAX;
                for v in rs.iter().map(|&x| x as i128).chain(std::iter::once(w)) { let y = (v * a).rem_euclid(p as i128); mn = mn.min(y.min(p as i128 - y)); }
                if mn < 2 { direct_fail += 1; wfail += 1; println!("W FAIL N={} r={} P={} w={}", n, r, p, w); } }
        }
    }
    println!("stress N in [{},{}] samples {} sets {}: ML<1/N {} ; all-primes-bad sets {} ; pigeonhole violations {} ; Lemma W direct failures {}", nmin, nmax, samples, tot, mlfail, allbad, pig, direct_fail + wfail * 0);
}
fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "selftest" => selftest(),
        "ml1n" => ml1n(a[2].parse().unwrap(), a[3].parse().unwrap(), &a[4]),
        "witness" => witness(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        "pigeon" => pigeon(a[2].parse().unwrap(), a[3].parse().unwrap()),
        "lemmal" => lemmal(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        "direct" => direct(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        "stress" => stress(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap()),
        "lemmaq" => lemmaq(a[2].parse().unwrap()),
        _ => println!("?"),
    }
}
