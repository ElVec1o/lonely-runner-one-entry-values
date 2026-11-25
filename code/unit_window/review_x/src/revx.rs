// revx.rs : fresh-author engine for THEOREM_X. Own code, not thx / br.rs.
// All arithmetic exact (i64 / i128 integers).  ML(V) = max_t min_{v in V} ||v t||.
// Route E1 (arc cover): "ML(V) >= p/q" <=> the open arcs {t: ||v t|| < p/q} do not cover [0,1/2].
// Route C  (candidates): ML(V) = max over t = k/(u+v), u<=v in V, of exact min_w ||w t||  (local maxima of a min of tents).
// usage: revx MODE [args]
use std::env;

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }

#[derive(Clone, Copy)]
struct Arc { l: i64, r: i64, v: i64 } // endpoints l/(q v), r/(q v)

// true iff exists t in [0,1/2] with ||v t|| >= p/q for every v in vs.
fn uncovered(vs: &[i64], p: i64, q: i64, buf: &mut Vec<Arc>) -> bool {
    buf.clear();
    for &v in vs { let jm = v / 2 + 1; for j in 0..=jm { buf.push(Arc { l: j * q - p, r: j * q + p, v }); } }
    buf.sort_unstable_by(|a, b| (a.l * b.v).cmp(&(b.l * a.v)));
    let mut reach: (i64, i64) = (0, 1); // reach.0 / (q * reach.1)
    let mut idx = 0usize; let n = buf.len();
    loop {
        let mut best = reach;
        while idx < n && buf[idx].l * reach.1 < reach.0 * buf[idx].v {
            let a = buf[idx];
            if a.r * best.1 > best.0 * a.v { best = (a.r, a.v); }
            idx += 1;
        }
        if best.0 * reach.1 > reach.0 * best.1 {
            reach = best;
            if 2 * reach.0 > q * reach.1 { return false; }
        } else { return true; }
    }
}

fn reduce(a: i64, b: i64) -> (i64, i64) { let g = gcd(a, b); if g == 0 { (a, b) } else { (a / g, b / g) } }

// Route C
fn ml_c(vs: &[i64]) -> (i64, i64) {
    let mut best = (0i64, 1i64);
    for i in 0..vs.len() { for j in i..vs.len() {
        let s = vs[i] + vs[j];
        for k in 0..=(s / 2) {
            let mut g = s;
            for &w in vs { let x = (w * k) % s; let d = x.min(s - x); if d < g { g = d; if g * best.1 <= best.0 * s { break; } } }
            if g * best.1 > best.0 * s { best = (g, s); }
        }
    } }
    reduce(best.0, best.1)
}

// exact ML via E1: bisection on theta = a/2^24, then unique m/s with s <= S in the cell, then exact confirmation.
fn ml_exact(vs: &[i64], buf: &mut Vec<Arc>) -> Option<(i64, i64)> {
    let q: i64 = 1 << 24;
    let smax = 2 * vs.iter().cloned().max().unwrap();
    let (mut lo, mut hi) = (0i64, (1i64 << 23) + 1);
    while hi - lo > 1 { let mid = (lo + hi) / 2; if uncovered(vs, mid, q, buf) { lo = mid } else { hi = mid } }
    let mut found: Option<(i64, i64)> = None;
    for s in 1..=smax {
        let m = (lo * s + q - 1) / q;
        if m * q < (lo + 1) * s {
            let f = reduce(m, s);
            match found { None => found = Some(f), Some(g) => if g != f { return None; } }
        }
    }
    let (m, s) = found?;
    let z = 8 * smax * smax;
    if !uncovered(vs, m, s, buf) { return None; }
    if uncovered(vs, m * z + 1, s * z, buf) { return None; }
    Some((m, s))
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } fn below(&mut self, n: u64) -> u64 { self.next() % n } }

fn build_b(n: i64, r: i64) -> Vec<i64> { (1..=n).filter(|&v| v != r).collect() }
fn d0_of(n: i64, r: i64) -> i64 { let mut d = n + 1 + r; while gcd(d, r) != 1 { d += 1; } d }
fn window(n: i64, r: i64, shift: i64) -> Vec<i64> { ((n + r + 1 + shift)..=(n + 2 * r + shift)).filter(|&d| d > 0 && gcd(d, r) == 1).collect() }
fn phi(n: i64) -> i64 { (1..=n).filter(|&k| gcd(k, n) == 1).count() as i64 }

// independent run-form: ell*(r) = max{ ell >= 0 : every m in [ell+1, 2 ell] has gcd(m,r) > 1 }, ell scanned to 6r
fn ellstar(r: i64) -> i64 {
    let mut best = 0;
    for ell in 0..=(6 * r) { if ((ell + 1)..=(2 * ell)).all(|m| gcd(m, r) > 1) { best = ell; } }
    best
}
fn run_ok(r: i64, ell: i64) -> bool { ((ell + 1)..=(2 * ell)).all(|m| gcd(m, r) > 1) }

const AUTH_TABLE: &str = "2,1,1,7,4; 3,2,0,9,4; 4,2,1,13,6; 5,4,0,15,6; 6,2,2,20,9; 7,6,0,21,8; 8,4,1,25,10; 9,6,0,27,10; 10,4,3,33,13; 11,10,0,33,12; 12,4,2,38,15; 13,12,0,39,14; 14,6,1,43,16; 15,8,0,45,16; 16,8,1,49,18; 17,16,0,51,18; 18,6,2,56,21; 19,18,0,57,20; 20,8,3,63,23; 21,12,0,63,22; 22,10,1,67,24; 23,22,0,69,24; 24,8,2,74,27; 25,20,0,75,26; 26,12,1,79,28; 27,18,0,81,28; 28,12,1,85,30; 29,28,0,87,30; 30,8,3,93,34; 31,30,0,93,32; 32,16,1,97,34; 33,20,0,99,34; 34,16,1,103,36; 35,24,0,105,36; 36,12,2,110,39; 37,36,0,111,38; 38,18,1,115,40; 39,24,0,117,40; 40,16,3,123,43; 41,40,0,123,42; 42,12,5,131,46; 43,42,0,129,44; 44,20,1,133,46; 45,24,0,135,46; 46,22,1,139,48; 47,46,0,141,48; 48,16,2,146,51; 49,42,0,147,50; 50,20,3,153,53; 51,32,0,153,52; 52,24,1,157,54; 53,52,0,159,54; 54,18,2,164,57; 55,40,0,165,56; 56,24,1,169,58; 57,36,0,171,58; 58,28,1,175,60; 59,58,0,177,60; 60,16,3,183,64";

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a.get(1).map(|s| s.as_str()).unwrap_or("");
    let mut buf: Vec<Arc> = Vec::new();
    match mode {
        // ---------------- instrument controls ----------------
        "ctl" => {
            let mut fails = 0;
            // [N]: ML = 1/(N+1) (Dirichlet + sharpness), both routes where cheap
            for n in 1..=60i64 {
                let v: Vec<i64> = (1..=n).collect();
                let ok1 = uncovered(&v, 1, n + 1, &mut buf);
                // just above 1/(N+1): (2*(N+1)*? ) use theta = 1/(N+1) + 1/(4 (N+1)^2)
                let z = 4 * (n + 1) * (n + 1);
                let above = uncovered(&v, z + (n + 1), (n + 1) * z, &mut buf);
                if !(ok1 && !above) { fails += 1; println!("FAIL [N] N={} at={} above={}", n, ok1, above); }
                if n <= 16 { let c = ml_c(&v); if c != (1, n + 1) { fails += 1; println!("FAIL routeC [N] N={} got {:?}", n, c); } }
            }
            // planted wrong claims: [10] ML >= 1/10 must be FALSE ; ML >= 1/12 TRUE
            let v10: Vec<i64> = (1..=10).collect();
            if uncovered(&v10, 1, 10, &mut buf) { fails += 1; println!("FAIL planted [10]>=1/10 accepted"); }
            if !uncovered(&v10, 1, 12, &mut buf) { fails += 1; println!("FAIL [10]>=1/12 rejected"); }
            // route C vs E1 on random sets, at the value and one step either side
            let mut rng = Rng(0x9E3779B97F4A7C15);
            let mut cnt = 0;
            for _ in 0..3000 {
                let m = 2 + rng.below(7) as usize; let mx = (m as u64) + 2 + rng.below(40);
                let mut s: Vec<i64> = Vec::new();
                while s.len() < m { let x = 1 + rng.below(mx) as i64; if !s.contains(&x) { s.push(x); } }
                let c = ml_c(&s);
                let e = ml_exact(&s, &mut buf);
                if e != Some(c) { fails += 1; println!("FAIL xval set {:?} routeC {:?} E1 {:?}", s, c, e); }
                cnt += 1;
            }
            println!("ctl: random sets cross-validated {} ; failures total {}", cnt, fails);
        }
        // ---------------- pointwise lemma tests (exact rationals) ----------------
        "lem" => {
            let (mut n1, mut bad1, mut n2, mut bad2) = (0u64, 0u64, 0u64, 0u64);
            let mm = 24i64;
            for r in 2..=40i64 { for n in (2 * r)..=(3 * r + 10) {
                let b = build_b(n, r);
                for c in 1..=(2 * r) { if gcd(c, r) != 1 { continue; }
                    // u(c) = -c^{-1} mod r
                    let u = (1..=r).find(|&v| (v * c) % r == r - 1 || (r == 1)).unwrap();
                    let x = n - ((n - u).rem_euclid(r));
                    let d = 2 * r + x;
                    for i in 0..=mm {
                        let q = r * (n + 1) * mm; let t = c * (n + 1) * mm + i;
                        let fb = b.iter().map(|&v| { let y = (v * t) % q; y.min(q - y) }).min().unwrap();
                        let pa = 2 * i * r; let pb = (n + 1) * mm - x * i;
                        n1 += 1; if fb != pa.min(pb) { bad1 += 1; if bad1 < 5 { println!("L1 mismatch r={} N={} c={} i={} fb={} pred={}", r, n, c, i, fb, pa.min(pb)); } }
                        // Lemma 2
                        let y = (d * t) % q; let nd = y.min(q - y);
                        let diff = (pa - pb).abs();
                        n2 += 1; if 2 * diff <= q && nd != diff { bad2 += 1; if bad2 < 5 { println!("L2 mismatch r={} N={} c={} i={}", r, n, c, i); } }
                        if !(d >= n + r + 1 && d <= n + 2 * r && gcd(d, r) == 1) { bad2 += 1; println!("L2 D not in W"); }
                    }
                }
            } }
            println!("Lemma1 f_B(t)=min(a,b): {} points, {} bad ; Lemma2 ||Dt||=|a-b| (+D in W): {} points, {} bad", n1, bad1, n2, bad2);
            // Lemma 3 at eta0 = 1/(2N)
            let (mut n3, mut bad3) = (0u64, 0u64);
            for r in 2..=60i64 { for n in (2 * r)..=(3 * r + 30) {
                let b = build_b(n, r); let w = window(n, r, 0);
                let q = 2 * n * r;
                for c in 1..=r { if gcd(c, r) != 1 { continue; }
                    let t = 2 * n * c + 1;
                    let u = (1..=r).find(|&v| (v * c) % r == r - 1).unwrap();
                    let x = n - ((n - u).rem_euclid(r)); let dc = 2 * r + x;
                    let fb = b.iter().map(|&v| { let y = (v * t) % q; y.min(q - y) }).min().unwrap();
                    n3 += 1; if fb != 2 * r { bad3 += 1; println!("L3a fail r={} N={} c={}", r, n, c); }
                    for &d in &w { let y = (d * t) % q; let nd = y.min(q - y);
                        if d == dc { if nd != 2 * n - d { bad3 += 1; println!("L3c fail r={} N={} c={} D={}", r, n, c, d); } }
                        else if nd < 2 * n { bad3 += 1; println!("L3b fail r={} N={} c={} D={} nd={}", r, n, c, d, nd); }
                    }
                }
            } }
            println!("Lemma3 (a)(b)(c): {} (r,N,c) triples, {} bad", n3, bad3);
        }
        // ---------------- main iff (ii) and the one-entry value ML(B)=2/D0 ----------------
        "iff" => {
            let rmax: i64 = a[2].parse().unwrap(); let ext: i64 = a[3].parse().unwrap();
            let do_b = a.get(4).map(|s| s == "b").unwrap_or(false);
            let mut tot = 0u64; let (mut mism, mut mb) = (0u64, 0u64);
            let (mut ma, mut mbb, mut mc) = (0u64, 0u64, 0u64);
            let mut nexc = 0u64;
            let mut table: Vec<(i64, i64, i64)> = Vec::new(); // r, last exc N, count in [2r,250]
            for r in 2..=rmax {
                let (mut last, mut cnt250) = (0i64, 0i64);
                let mut excs: Vec<i64> = Vec::new();
                for n in (2 * r)..=(3 * r + ext) {
                    let b = build_b(n, r); let w = window(n, r, 0);
                    let d0 = d0_of(n, r); assert!(w.iter().min().copied() == Some(d0));
                    if w.len() as i64 != phi(r) { println!("PHI MISMATCH r={} N={}", r, n); }
                    let mut v = b.clone(); v.extend_from_slice(&w);
                    let exc = !uncovered(&v, 1, n, &mut buf); // ML < 1/N
                    let pred = d0 > 2 * n - 2 * r;
                    tot += 1; if exc != pred { mism += 1; println!("MISMATCH r={} N={} D0={} engine_exc={} pred={}", r, n, d0, exc, pred); }
                    // planted wrong criteria (off by one etc.)
                    if exc != (d0 >= 2 * n - 2 * r) { ma += 1; }
                    if exc != (d0 > 2 * n - 2 * r + 1) { mbb += 1; }
                    if exc != (d0 > 2 * n - 2 * r - 2) { mc += 1; }
                    if exc { nexc += 1; last = n; excs.push(n); if n <= 250 { cnt250 += 1; } }
                    if do_b {
                        let z = 8 * n * n;
                        let t1 = uncovered(&b, 2, d0, &mut buf);
                        let t2 = uncovered(&b, 2 * z + d0, d0 * z, &mut buf);
                        if !(t1 && !t2) { mb += 1; println!("ML(B)!=2/D0 r={} N={} D0={} at={} above={}", r, n, d0, t1, t2); }
                    }
                }
                table.push((r, last, cnt250));
                if r == 42 { println!("r=42 exceptional N in [126,140]: {:?}", excs.iter().filter(|&&x| x <= 140).collect::<Vec<_>>()); }
                if r % 10 == 0 { println!("progress r={} done, pairs so far {}, mismatches {}", r, tot, mism); }
            }
            println!("IFF: pairs {} ; exceptional {} ; mismatches(true criterion) {} ; ML(B)=2/D0 failures {} (checked={})", tot, nexc, mism, mb, do_b);
            println!("planted wrong criteria mismatch counts over same grid: D0>=2N-2r : {} ; D0>2N-2r+1 : {} ; D0>2N-2r-2 : {}", ma, mbb, mc);
            // compare last-failing N with run-form and with author's table
            let mut badlast = 0;
            for &(r, last, cnt) in &table {
                let ls = ellstar(r);
                if last != 3 * r + ls { badlast += 1; println!("LAST MISMATCH r={} engine {} runform {}", r, last, 3 * r + ls); }
                if r <= 60 {
                    for ent in AUTH_TABLE.split(';') {
                        let f: Vec<i64> = ent.trim().split(',').map(|x| x.parse().unwrap()).collect();
                        if f[0] == r {
                            if f[1] != phi(r) || f[2] != ls || f[3] != last || f[4] != cnt { badlast += 1; println!("AUTH TABLE MISMATCH r={} auth {:?} mine phi={} ell*={} last={} cnt={}", r, f, phi(r), ls, last, cnt); }
                        }
                    }
                }
            }
            println!("last-failing-N: engine vs run-form (all r<={}) and vs author table (r<=60): {} mismatches over {} values of r", rmax, badlast, table.len());
        }
        // ---------------- minimality of W and planted negatives ----------------
        "neg" => {
            let rmax: i64 = a[2].parse().unwrap();
            let (mut npairs, mut ndrops, mut dropbad) = (0u64, 0u64, 0u64);
            let mut shiftbroken = [0u64; 4]; let shifts = [-2i64, -1, 1, 2];
            let (mut no2r, mut no2rbroken) = (0u64, 0u64);
            for r in 2..=rmax {
                for n in (2 * r)..=(4 * r) {
                    let b = build_b(n, r); let w = window(n, r, 0);
                    let mut v = b.clone(); v.extend_from_slice(&w);
                    if uncovered(&v, 1, n, &mut buf) { continue; } // not exceptional
                    npairs += 1;
                    for (i, &d) in w.iter().enumerate() {
                        let mut v2 = b.clone(); for (j, &x) in w.iter().enumerate() { if j != i { v2.push(x); } }
                        ndrops += 1;
                        if !uncovered(&v2, 1, n, &mut buf) { dropbad += 1; println!("DROP leaves exception r={} N={} D={}", r, n, d); }
                    }
                    for (si, &s) in shifts.iter().enumerate() {
                        let ws = window(n, r, s); let mut v2 = b.clone(); v2.extend_from_slice(&ws);
                        if uncovered(&v2, 1, n, &mut buf) { shiftbroken[si] += 1; }
                    }
                    // planted: delete 2r from B (Lemma 1 needs 2r in B) -- expect many breaks
                    let mut v3: Vec<i64> = b.iter().cloned().filter(|&x| x != 2 * r).collect(); v3.extend_from_slice(&w);
                    no2r += 1; if uncovered(&v3, 1, n, &mut buf) { no2rbroken += 1; }
                }
            }
            println!("NEG: exceptional pairs (r<={}, N in [2r,4r]) {} ; drop-one sets {} ; drop leaves the exception (minimality violated): {}", rmax, npairs, ndrops, dropbad);
            println!("planted shifted windows, broken/exceptional pairs: shift-2 {} ; shift-1 {} ; shift+1 {} ; shift+2 {} (of {})", shiftbroken[0], shiftbroken[1], shiftbroken[2], shiftbroken[3], npairs);
            println!("planted: 2r deleted from B: {} / {} exceptions broken", no2rbroken, no2r);
        }
        // ---------------- arithmetic: (iii), (iv) bounds, table of values ----------------
        "arith" => {
            let rm: i64 = a[2].parse().unwrap();
            let (mut c3, mut b3) = (0u64, 0u64);
            for r in 2..=rm { for ell in 0..=300i64 {
                let n = 3 * r + ell; let d0 = d0_of(n, r);
                c3 += 1; if (d0 > 2 * n - 2 * r) != run_ok(r, ell) { b3 += 1; println!("(iii) mismatch r={} ell={}", r, ell); }
            } }
            println!("(iii) D0>2N-2r vs run [ell+1,2ell] free of coprimes: {} cases, {} bad (r<={})", c3, b3, rm);
            // N in [2r,3r]: always exceptional by D0 test
            let mut bad_le3 = 0; for r in 2..=rm.min(400) { for n in (2 * r)..=(3 * r) { if !(d0_of(n, r) > 2 * n - 2 * r) { bad_le3 += 1; } } }
            println!("N in [2r,3r] always D0>2N-2r: {} violations (r<=min(rm,400))", bad_le3);
            // bounds on ell*
            let smallprime = |r: i64| -> i64 { let mut p = 2; loop { if (2..p).all(|d| p % d != 0) && r % p != 0 { return p; } p += 1; } };
            let pplus = |r: i64| -> i64 { let mut m = r; let mut best = 1; let mut p = 2; while m > 1 { if m % p == 0 { best = p; while m % p == 0 { m /= p; } } p += 1; } best };
            let jac = |r: i64| -> i64 { let mut m = 1; loop { if (1..=(4 * r + 4)).all(|s| (s..(s + m)).any(|x| gcd(x, r) == 1)) { return m; } m += 1; } };
            let (mut bb, mut maxl, mut oddbad, mut n_noninterval) = (0, (0, 0), 0, 0);
            let jr = rm.min(200);
            for r in 2..=rm.min(2000) {
                let ls = ellstar(r);
                let q = smallprime(r);
                if ls < (q - 1) / 2 { bb += 1; println!("lower bound fails r={}", r); }
                if ls >= pplus(r) { bb += 1; println!("upper bound P+ fails r={}", r); }
                if r % 2 == 1 && ls != 0 { oddbad += 1; }
                if r <= jr && ls > jac(r) - 1 { bb += 1; println!("Jacobsthal bound fails r={}", r); }
                if ls > maxl.0 { maxl = (ls, r); }
                // non-interval: exceptional ell set (ell>=0, ell<=2r) has a gap below its max
                if r <= 200 { let ex: Vec<bool> = (0..=ls).map(|e| run_ok(r, e)).collect(); if ex.iter().any(|&x| !x) { n_noninterval += 1; } }
            }
            println!("ell* bounds floor((q-1)/2)<=ell*<P+(r) (r<=2000), ell*<=j(r)-1 (r<={}) : {} failures ; odd r with ell*!=0: {} ; max ell* = {} at r={} ; r<=200 with gap in ell-set below ell*: {}", jr, bb, oddbad, maxl.0, maxl.1, n_noninterval);
            // primorials
            for (r, pnext) in [(2i64, 3i64), (6, 5), (30, 7), (210, 11), (2310, 13), (30030, 17)] {
                let ls = ellstar(r); println!("primorial r={} ell*={} formula floor((P'-1)/2)={} {}", r, ls, (pnext - 1) / 2, if ls == (pnext - 1) / 2 { "ok" } else { "BAD" });
            }
            println!("r=42: ell=3 ok? {} ; ell=4 ok? {} ; ell=5 ok? {} ; ell=6 ok? {}", run_ok(42, 3), run_ok(42, 4), run_ok(42, 5), run_ok(42, 6));
            // table of values: best 3r+ell*+1 over phi(r)<=k
            let ks = [1i64, 2, 3, 4, 6, 8, 10, 12, 16, 20, 24, 32, 48];
            let auth: [(i64, i64, i64); 11] = [(2, 21, 6), (4, 39, 12), (6, 57, 18), (8, 94, 30), (10, 94, 30), (12, 132, 42), (16, 184, 60), (20, 201, 66), (24, 274, 90), (32, 364, 120), (48, 636, 210)];
            let rscan = 3000i64;
            let phis: Vec<i64> = (0..=rscan).map(|r| if r == 0 { 0 } else { phi(r) }).collect();
            for &k in &ks {
                let mut best = (0i64, 0i64);
                for r in 2..=rscan { if phis[r as usize] <= k { let v = 3 * r + ellstar(r) + 1; if v > best.0 { best = (v, r); } } }
                let au = auth.iter().find(|x| x.0 == k);
                let tag = match au { Some(x) => if (x.1, x.2) == best { "matches author".to_string() } else { format!("AUTHOR DIFFERS {:?}", x) }, None => "-".to_string() };
                println!("k={:3}: best 3r+ell*+1 = {} at r={} ; {}", k, best.0, best.1, tag);
            }
        }
        // ---------------- growth numerics ----------------
        "growth" => {
            let lim: usize = 7_000_000;
            let mut ph: Vec<u32> = (0..=lim as u32).collect();
            for p in 2..=lim { if ph[p] == p as u32 { let mut m = p; while m <= lim { ph[m] -= ph[m] / p as u32; m += p; } } }
            // R(k) = max{r: phi(r) <= k}: valid if every r > lim has phi(r) > k.
            let ks = [4usize, 16, 1000, 10000, 92160, 100000, 480480, 1000000];
            let eg = 0.5772156649015329f64;
            for &k in &ks {
                let mut rr = 0usize; for r in 2..=lim { if ph[r] as usize <= k { rr = r; } }
                let kk = k as f64; let ll = kk.ln().ln();
                println!("k={:8} R(k)={:8} (3R+1)/(k loglog k)={:.2} ; R/(k loglog k)={:.3} (e^gamma={:.3}) ; phi at lim edge ok? min phi over r in (R,lim] = {}", k, rr, (3.0 * rr as f64 + 1.0) / (kk * ll), rr as f64 / (kk * ll), eg.exp(), ((rr + 1)..=lim).map(|r| ph[r]).min().unwrap_or(0));
            }
        }
        // exact ML(V) as a fraction (E1 bisection, confirmed two-sided) vs 1/N, small grid
        "mlv" => {
            let rmax: i64 = a[2].parse().unwrap(); let ext: i64 = a[3].parse().unwrap();
            let (mut tot, mut none, mut bad, mut eq_n) = (0u64, 0u64, 0u64, 0u64);
            let mut ex_count = 0u64; let mut worst_exc = (0i64, 1i64, 0i64, 0i64); // largest N*ML among exceptional
            let mut worst_non = (1_000_000i64, 1i64, 0i64, 0i64); // smallest N*ML among non-exceptional
            for r in 2..=rmax { for n in (2 * r)..=(3 * r + ext) {
                let b = build_b(n, r); let w = window(n, r, 0); let d0 = d0_of(n, r);
                let mut v = b; v.extend_from_slice(&w);
                tot += 1;
                match ml_exact(&v, &mut buf) {
                    None => { none += 1; println!("ml_exact None r={} N={}", r, n); }
                    Some((m, s)) => {
                        let exc = m * n < s; // ML < 1/N  <=>  m/s < 1/N
                        if exc != (d0 > 2 * n - 2 * r) { bad += 1; println!("BAD r={} N={} ML={}/{}", r, n, m, s); }
                        if m * n == s { eq_n += 1; }
                        // N*ML = m n / s as fraction compare
                        if exc { if m * n * worst_exc.1 > worst_exc.0 * s { worst_exc = (m * n, s, r, n); } ex_count += 1; }
                        else { if m * n * worst_non.1 < worst_non.0 * s { worst_non = (m * n, s, r, n); } }
                    }
                }
            } }
            println!("MLV: {} pairs, exact ML(V) found for all but {} ; exception-vs-criterion mismatches {} ; ML exactly 1/N in {} pairs ; exceptional {}", tot, none, bad, eq_n, ex_count);
            println!("largest N*ML(V) among exceptional: {}/{} at r={} N={} ; smallest N*ML(V) among non-exceptional: {}/{} at r={} N={}", worst_exc.0, worst_exc.1, worst_exc.2, worst_exc.3, worst_non.0, worst_non.1, worst_non.2, worst_non.3);
        }
        _ => println!("modes: ctl lem iff neg arith growth mlv"),
    }
}
