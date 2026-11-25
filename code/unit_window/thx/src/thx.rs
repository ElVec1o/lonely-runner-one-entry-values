// thx.rs : own exact engine for Theorem X review. Independent of br.rs (not read).
// Decision engine: ML(V) >= p/q  iff the OPEN arcs {t : ||v t|| < p/q}, v in V, do NOT cover the circle.
// All arithmetic in i64 integers: arc endpoints are (j q -+ p)/(q v); comparison a/(q v) < b/(q v') <=> a v' < b v.
// Route C (independent): ML(V) = max over t = k/(u+v), u<=v in V, of min_v ||v t|| (exact residues).
use std::env;
use std::collections::BTreeSet;

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a } else { gcd(b, a % b) } }

struct Arc { l: i64, r: i64, v: i64 }

// None  => covered (no t in [0,1/2] with f_V(t) >= p/q); Some(num,den) => uncovered point t=num/den.
fn covered(vs: &[i64], p: i64, q: i64, buf: &mut Vec<Arc>) -> Option<(i64, i64)> {
    buf.clear();
    for &v in vs {
        let mut j = 0i64;
        while j <= v / 2 + 1 {
            let l = j * q - p;
            if 2 * l < q * v { buf.push(Arc { l, r: j * q + p, v }); }
            j += 1;
        }
    }
    buf.sort_unstable_by(|a, b| (a.l * b.v).cmp(&(b.l * a.v)));
    let (mut cn, mut cv) = (0i64, 1i64);
    for a in buf.iter() {
        if 2 * cn > q * cv { return None; }
        if a.l * cv < cn * a.v {
            if a.r * cv > cn * a.v { cn = a.r; cv = a.v; }
        } else {
            return Some((cn, q * cv));
        }
    }
    if 2 * cn > q * cv { None } else { Some((cn, q * cv)) }
}

fn ml_ge(vs: &[i64], p: i64, q: i64, buf: &mut Vec<Arc>) -> bool { covered(vs, p, q, buf).is_some() }

// route C: exact ML as fraction (num, den)
fn ml_exact(vs: &[i64]) -> (i64, i64) {
    let mut qs = BTreeSet::new();
    for (i, &u) in vs.iter().enumerate() { for &v in &vs[i..] { qs.insert(u + v); } }
    let (mut bn, mut bd) = (0i64, 1i64);
    for &q in &qs {
        for k in 0..=q / 2 {
            let mut m = q; // min residue distance
            for &v in vs {
                let y = (v * k) % q;
                let d = if y < q - y { y } else { q - y };
                if d < m { m = d; if m * bd <= bn * q { break; } }
            }
            if m * bd > bn * q { bn = m; bd = q; }
        }
    }
    let g = gcd(bn, bd); (bn / g, bd / g)
}

fn d0(n: i64, r: i64) -> i64 { let mut d = n + 1 + r; while gcd(d, r) != 1 { d += 1; } d }
fn phi(r: i64) -> i64 { (1..=r).filter(|&x| gcd(x, r) == 1).count() as i64 }
fn base(n: i64, r: i64) -> Vec<i64> { (1..=n).filter(|&x| x != r).collect() }
fn wset(n: i64, r: i64, lo: i64, hi: i64) -> Vec<i64> { (lo..=hi).filter(|&d| gcd(d, r) == 1).collect() }
fn fam(n: i64, r: i64) -> Vec<i64> { let mut v = base(n, r); v.extend(wset(n, r, n + r + 1, n + 2 * r)); v }
// largest l >= 0 with gcd(m, r) > 1 for all m in [l+1, 2l]
fn ell_star(r: i64) -> i64 {
    let mut best = 0;
    for l in 0..=(2 * r + 5) { if ((l + 1)..=(2 * l)).all(|m| gcd(m, r) > 1) { best = l; } }
    best
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } fn below(&mut self, n: u64) -> u64 { self.next() % n } }

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a[1].as_str();
    let mut buf: Vec<Arc> = Vec::new();
    match mode {
        "ctl" => {
            let mut bad = 0;
            // [N]: ML = 1/(N+1)
            for n in 3..=40i64 {
                let v: Vec<i64> = (1..=n).collect();
                let ok = ml_ge(&v, 1, n + 1, &mut buf) && !ml_ge(&v, 1, n, &mut buf) && !ml_ge(&v, 1001, 1000 * (n + 1), &mut buf);
                let c = ml_exact(&v);
                if !ok || c != (1, n + 1) { bad += 1; println!("CTL FAIL [N] N={} routeC={:?}", n, c); }
            }
            println!("ctl [N] N=3..40: fails so far {}", bad);
            // known values (value, speeds)
            let cases: Vec<(i64, i64, Vec<i64>, &str)> = vec![
                (1, 5, vec![1, 3, 4, 7], "ML(1,3,4,7)=1/5"),
                (5, 33, vec![1, 5, 6, 11, 16, 17], "ML(1,5,6,11,16,17)=5/33"),
                (1, 9, (1..=8).collect(), "[8]=1/9"),
            ];
            for (n, d, v, name) in cases {
                let ok = ml_ge(&v, n, d, &mut buf) && !ml_ge(&v, n * 1000 + 1, d * 1000, &mut buf);
                let c = ml_exact(&v);
                println!("{} engine_ok={} routeC={:?}", name, ok, c);
                if !ok || c != (n, d) { bad += 1; }
            }
            // [13]-6+69 = 3/40 ; [20]-6+{29,31} = 2/41 ; [13]-12+36 = 3/41
            let mut s = base(13, 6); s.push(69);
            let ok1 = ml_ge(&s, 3, 40, &mut buf) && !ml_ge(&s, 3001, 40000, &mut buf);
            println!("[13]-6+69 = 3/40 : engine_ok={} routeC={:?}", ok1, ml_exact(&s));
            let mut s = base(20, 6); s.push(29); s.push(31);
            let ok2 = ml_ge(&s, 2, 41, &mut buf) && !ml_ge(&s, 2001, 41000, &mut buf);
            println!("[20]-6+{{29,31}} = 2/41 : engine_ok={} routeC={:?} below 1/20: {}", ok2, ml_exact(&s), !ml_ge(&s, 1, 20, &mut buf));
            let mut s = base(13, 12); s.push(36);
            let ok3 = ml_ge(&s, 3, 41, &mut buf) && !ml_ge(&s, 3001, 41000, &mut buf);
            println!("[13]-12+36 = 3/41 : engine_ok={} routeC={:?}", ok3, ml_exact(&s));
            if !(ok1 && ok2 && ok3) { bad += 1; }
            // [21]-6+{29,31} must be >= 1/21
            let mut s = base(21, 6); s.push(29); s.push(31);
            let ok4 = ml_ge(&s, 1, 21, &mut buf);
            println!("[21]-6+{{29,31}} >= 1/21 : {} (predicted by D0=29<=2N-2r=30: not an exception)", ok4);
            if !ok4 { bad += 1; }
            // negative planted: wrong claims must be rejected
            let v: Vec<i64> = (1..=10).collect();
            let rej = !ml_ge(&v, 1, 10, &mut buf) && ml_ge(&v, 1, 12, &mut buf);
            println!("planted wrong claims on [10] (ML>=1/10 false, ML>=1/12 true): {}", rej);
            if !rej { bad += 1; }
            // xval: engine decision vs route C on random sets
            let mut rng = Rng(0x9e3779b97f4a7c15);
            let mut mism = 0; let mut tot = 0;
            for _ in 0..20000 {
                let m = 2 + rng.below(8) as usize; let mx = m as u64 + 2 + rng.below(70);
                let mut s: BTreeSet<i64> = BTreeSet::new();
                while s.len() < m { s.insert(1 + rng.below(mx) as i64); }
                let v: Vec<i64> = s.into_iter().collect();
                let (nn, dd) = ml_exact(&v);
                let ok = ml_ge(&v, nn, dd, &mut buf) && !ml_ge(&v, nn * 1000 + 1, dd * 1000, &mut buf) && ml_ge(&v, nn * 1000 - 1, dd * 1000, &mut buf);
                tot += 1; if !ok { mism += 1; if mism < 5 { println!("XVAL MISMATCH {:?} routeC={}/{}", v, nn, dd); } }
            }
            println!("xval engine vs route C, 20000 random sets, value and one step either side: {} mismatches of {}", mism, tot);
            if mism > 0 { bad += 1; }
            println!("CTL SUMMARY fails={}", bad);
        }
        "eq" => {
            // args: rmax nmax
            let rmax: i64 = a[2].parse().unwrap(); let nmax: i64 = a[3].parse().unwrap();
            let data: [(i64, i64); 10] = [(2, 7), (4, 13), (6, 20), (10, 33), (12, 38), (18, 56), (24, 74), (30, 93), (42, 131), (60, 183)];
            let (mut tot, mut mis1, mut mis2, mut lowtot, mut lowexc) = (0u64, 0u64, 0u64, 0u64, 0u64);
            let (mut pb_tot, mut pb_fail) = (0u64, 0u64);
            println!("r phi(r) ell* | lastExc(engine, N>=2r) formula=3r+ell* | reference-data | #exc(N>=2r) #pred | mismatches | exceptions below 2r (N in [ceil(3r/2),2r))");
            for r in 2..=rmax {
                let lo = (3 * r + 1) / 2;
                let mut last = -1; let mut nexc = 0; let mut npred = 0; let mut rm = 0;
                let mut low = 0; let mut lown = 0;
                for n in lo..=nmax {
                    let v = fam(n, r);
                    let exc = !ml_ge(&v, 1, n, &mut buf);
                    if n >= 2 * r {
                        let pred = d0(n, r) > 2 * n - 2 * r;
                        tot += 1; if exc { nexc += 1; last = n; } if pred { npred += 1; }
                        if exc != pred { rm += 1; if exc { mis1 += 1 } else { mis2 += 1 }; println!("MISMATCH r={} N={} engine_exc={} pred={} D0={} 2N-2r={}", r, n, exc, pred, d0(n, r), 2 * n - 2 * r); }
                        // Theorem P: ML([N]\{r}) = 2/D0 (r <= N/2)
                        let b = base(n, r); let d = d0(n, r);
                        pb_tot += 1;
                        let ok = ml_ge(&b, 2, d, &mut buf) && !ml_ge(&b, 2001, 1000 * d, &mut buf);
                        if !ok { pb_fail += 1; println!("THM P FAIL r={} N={} D0={}", r, n, d); }
                    } else { lown += 1; if exc { low += 1; } }
                }
                lowtot += lown; lowexc += low;
                let f = 3 * r + ell_star(r);
                let fd = data.iter().find(|x| x.0 == r).map(|x| x.1.to_string()).unwrap_or("-".into());
                println!("{} {} {} | {} {} | {} | {} {} | {} | {}/{}", r, phi(r), ell_star(r), last, f, fd, nexc, npred, rm, low, lown);
            }
            println!("EQ SUMMARY pairs(N>=2r)={} mismatches: engine-exception-but-not-predicted={} predicted-but-engine-no-exception={} ; ThmP checks {} fails {} ; below-2r pairs {} with exception {}", tot, mis1, mis2, pb_tot, pb_fail, lowtot, lowexc);
        }
        "card" => {
            // |W| = phi(r) for every r<=2000, N in [2r,3r+60]; and ell* checks
            let mut bad = 0u64; let mut tot = 0u64;
            for r in 2..=2000i64 { let ph = phi(r); for n in 2 * r..=3 * r + 60 { tot += 1; if wset(n, r, n + r + 1, n + 2 * r).len() as i64 != ph { bad += 1; } } }
            println!("card |W|=phi(r): {} cases, {} failures", tot, bad);
            // equivalence of the two descriptions of the exception set, pure arithmetic: D0>2N-2r  <=>  all m in [l+1,2l] non-coprime to r, where N=3r+l (l>=1); N<=3r always true
            let mut bad2 = 0u64; let mut tot2 = 0u64;
            for r in 2..=3000i64 { for n in 2 * r..=3 * r + 400 { tot2 += 1;
                let lhs = d0(n, r) > 2 * n - 2 * r;
                let rhs = if n <= 3 * r { true } else { let l = n - 3 * r; ((l + 1)..=(2 * l)).all(|m| gcd(m, r) > 1) };
                if lhs != rhs { bad2 += 1; } } }
            println!("arith: (D0>2N-2r) <=> (all m in [l+1,2l] share a factor with r, N=3r+l): {} cases, {} failures", tot2, bad2);
            // ell* <= (j(r)-1) and ell* >= floor((q-1)/2), q least prime not dividing r ; and last exceptional N = 3r+ell*(r) (no exception at any N in (3r+ell*, 3r+400])
            let mut bad3 = 0u64; let mut maxell = 0i64; let mut maxr = 0;
            for r in 2..=20000i64 {
                let e = ell_star(r);
                // jacobsthal j(r): max gap between consecutive integers coprime to r (cyclic over one period r)
                let cop: Vec<i64> = (1..=r).filter(|&x| gcd(x, r) == 1).collect();
                let mut j = 0; for w in cop.windows(2) { if w[1] - w[0] > j { j = w[1] - w[0]; } } let wrap = cop[0] + r - cop[cop.len() - 1]; if wrap > j { j = wrap; }
                let mut q = 2; while r % q == 0 { q += 1; while (2..q).any(|d| q % d == 0) { q += 1; } }
                let lo = (q - 1) / 2;
                if !(e <= j - 1 && e >= lo) { bad3 += 1; println!("ELL BOUND FAIL r={} ell*={} j={} q={}", r, e, j, q); }
                if e > maxell { maxell = e; maxr = r; }
            }
            println!("ell*(r) in [floor((q-1)/2), j(r)-1] for all r in 2..=20000: {} failures; max ell* = {} at r = {}", bad3, maxell, maxr);
        }
        "nt" => {
            // growth table: R(k) = max{r : phi(r) <= k}; bound B(k)=3R(k)+1 ; compare with k loglog k
            let lim: usize = 7_000_000;
            let mut ph: Vec<u32> = (0..=lim as u32).collect();
            for p in 2..=lim { if ph[p] == p as u32 { let mut m = p; while m <= lim { ph[m] -= ph[m] / p as u32; m += p; } } }
            let mut best = vec![0u32; lim + 1];
            for r in 2..=lim { let f = ph[r] as usize; if (r as u32) > best[f] { best[f] = r as u32; } }
            for f in 1..=lim { if best[f - 1] > best[f] { best[f] = best[f - 1]; } }
            let g = 0.5772156649015329f64;
            println!("k  R(k)  3R(k)+1  k*loglog(k)  (3R+1)/(k loglog k)  3*e^gamma={:.4}", 3.0 * g.exp());
            for &k in &[2usize, 4, 6, 8, 12, 16, 24, 48, 96, 480, 1000, 5760, 10000, 92160, 100000, 480480, 1000000] {
                let r = best[k] as f64; let kk = k as f64; let ll = if kk > 3.0 { kk.ln().ln() } else { f64::NAN };
                println!("{} {} {} {:.1} {:.4}", k, best[k], 3 * best[k] as u64 + 1, kk * ll, (3.0 * r + 1.0) / (kk * ll));
            }
            // exact lower bound N0(k) >= max over r (phi(r)<=k) of 3r+ell*(r)+1, small k
            println!("small k exact: N0(k) >= max_r(3r+ell*(r)+1) over phi(r)<=k, r<=20000 vs 3R(k)+1");
            for &k in &[2usize, 4, 6, 8, 10, 12, 16, 20, 24, 32, 48] {
                let mut b = 0i64; let mut br = 0;
                for r in 2..=20000i64 { if ph[r as usize] as usize <= k { let v = 3 * r + ell_star(r) + 1; if v > b { b = v; br = r; } } }
                println!("k={} bound={} at r={} (3R+1={})", k, b, br, 3 * best[k] as i64 + 1);
            }
        }
        "neg" => {
            let rmax: i64 = a[2].parse().unwrap(); let nmax: i64 = a[3].parse().unwrap();
            let (mut np, mut drop_tot, mut drop_still) = (0u64, 0u64, 0u64);
            let shifts = [-2i64, -1, 1, 2];
            let mut sh_tot = [0u64; 4]; let mut sh_still = [0u64; 4];
            let (mut rep_tot, mut rep_still) = (0u64, 0u64);
            let (mut drop_pairs_all_needed, mut drop_pairs) = (0u64, 0u64);
            for r in 2..=rmax {
                for n in 2 * r..=nmax {
                    if d0(n, r) <= 2 * n - 2 * r { continue; }
                    np += 1;
                    let w = wset(n, r, n + r + 1, n + 2 * r);
                    let b = base(n, r);
                    // drop one element of W
                    let mut all_needed = true;
                    for i in 0..w.len() {
                        let mut v = b.clone(); for (j, &d) in w.iter().enumerate() { if j != i { v.push(d); } }
                        drop_tot += 1;
                        if !ml_ge(&v, 1, n, &mut buf) { drop_still += 1; all_needed = false; }
                    }
                    drop_pairs += 1; if all_needed { drop_pairs_all_needed += 1; }
                    // shifted windows (same length r, units of r)
                    for (si, &s) in shifts.iter().enumerate() {
                        let mut v = b.clone(); v.extend(wset(n, r, n + r + 1 + s, n + 2 * r + s));
                        sh_tot[si] += 1; if !ml_ge(&v, 1, n, &mut buf) { sh_still[si] += 1; }
                    }
                    // replace the first element D by D+r (same class mod r, one period higher)
                    if !w.is_empty() {
                        let mut v = b.clone(); for (j, &d) in w.iter().enumerate() { v.push(if j == 0 { d + r } else { d }); }
                        rep_tot += 1; if !ml_ge(&v, 1, n, &mut buf) { rep_still += 1; }
                    }
                }
            }
            println!("NEG pairs (r in 2..={}, N in 2r..={}, predicted exception): {}", rmax, nmax, np);
            println!("drop one element of W: {} planted sets; still exception (ML<1/N): {} ; detected as non-exception: {}", drop_tot, drop_still, drop_tot - drop_still);
            println!("pairs where EVERY single drop destroys the exception (W minimal): {} of {}", drop_pairs_all_needed, drop_pairs);
            for (si, &s) in shifts.iter().enumerate() { println!("window shifted by {:+}: {} sets, still exception {} ; broken {}", s, sh_tot[si], sh_still[si], sh_tot[si] - sh_still[si]); }
            println!("replace first D by D+r: {} sets, still exception {} ; broken {}", rep_tot, rep_still, rep_tot - rep_still);
        }
        _ => println!("modes: ctl | eq rmax nmax | neg rmax nmax"),
    }
}
