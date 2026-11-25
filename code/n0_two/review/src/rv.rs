// Review engine for N0(2) = 21. Exact integer arithmetic only.
// Units: tau = 1/N. Good set of speed v: {t in [0,1/2] : ||v t|| >= 1/N} (closed). Band of v: open interval ((kN-1)/(vN),(kN+1)/(vN)).
// Modes:
//   cert N0 N1 R [SAB]   reduction certificate (M1 + one-speed gap + exact tail), R = h (r<=N/2) | mK (r<=N-K); SAB divides thresholds
//   one N r              print G0 pieces, W0, exceptions with exact ML
//   brute N0 N1 R WMAX   exact brute force over all N<w1<w2<=WMAX by left-endpoint candidates (no use of W0/T)
//   xcheck N0 N1 R WMAX  cert vs brute, set comparison for pairs with w2<=WMAX
//   mlscan N r WMAX      all pairs w<=WMAX: decision by ML sum-candidates vs brute decision
//   ctl                  controls
use std::env;

type I = i128;
#[derive(Clone, Copy, Debug)]
struct Q { p: I, q: I }
impl Q {
    fn new(p: I, q: I) -> Q { if q < 0 { Q { p: -p, q: -q } } else { Q { p, q } } }
    fn lt(&self, o: &Q) -> bool { self.p * o.q < o.p * self.q }
    fn le(&self, o: &Q) -> bool { self.p * o.q <= o.p * self.q }
    fn sub(&self, o: &Q) -> Q { Q { p: self.p * o.q - o.p * self.q, q: self.q * o.q } }
    fn f(&self) -> f64 { self.p as f64 / self.q as f64 }
}
#[derive(Clone, Copy, Debug)]
struct Pc { a: Q, b: Q }

fn complement(speeds: &[i64], n: i64) -> Vec<Pc> {
    let n_ = n as I;
    let half = Q::new(1, 2);
    let mut bands: Vec<(Q, Q)> = Vec::new();
    for &v in speeds {
        let v = v as I;
        let mut k: I = 0;
        loop {
            // left end (kN-1)/(vN) ; stop when >= 1/2
            if 2 * (k * n_ - 1) >= v * n_ { break; }
            bands.push((Q::new(k * n_ - 1, v * n_), Q::new(k * n_ + 1, v * n_)));
            k += 1;
        }
    }
    bands.sort_by(|x, y| (x.0.p * y.0.q).cmp(&(y.0.p * x.0.q)));
    let mut c = Q::new(0, 1);
    let mut out = Vec::new();
    let mut done = false;
    for (l, r) in bands {
        if !c.le(&half) { done = true; break; }
        if c.le(&l) {
            let hi = if l.lt(&half) { l } else { half };
            if c.le(&hi) { out.push(Pc { a: c, b: hi }); }
        }
        if c.lt(&r) { c = r; }
    }
    if !done && c.le(&half) { out.push(Pc { a: c, b: half }); }
    out
}

// intersect pieces with good(w); returns pieces (maybe degenerate)
fn restrict(ps: &[Pc], w: i64, n: i64, stop_first: bool) -> Vec<Pc> {
    let (w, n) = (w as I, n as I);
    let mut out = Vec::new();
    for pc in ps {
        let mut t = pc.a;
        loop {
            if pc.b.lt(&t) { break; }
            let x = w * t.p;
            let m = x.div_euclid(t.q);
            let rem = x - m * t.q;
            if n * rem < t.q {
                t = Q::new(m * n + 1, w * n);
            } else if n * (t.q - rem) < t.q {
                t = Q::new((m + 1) * n + 1, w * n);
            } else {
                let end = Q::new((m + 1) * n - 1, w * n);
                let hi = if end.lt(&pc.b) { end } else { pc.b };
                out.push(Pc { a: t, b: hi });
                if stop_first { return out; }
                if pc.b.le(&end) { break; }
                t = Q::new((m + 1) * n + 1, w * n);
            }
        }
    }
    out
}

fn longest(ps: &[Pc]) -> Option<Q> {
    let mut best: Option<Q> = None;
    for pc in ps {
        let l = pc.b.sub(&pc.a);
        if l.p > 0 { match best { None => best = Some(l), Some(b) => if b.lt(&l) { best = Some(l) } } }
    }
    best
}

struct Res { exc: Vec<(i64, i64)>, fam: Vec<i64>, deg: bool, w0: i64, tmax: i64, g0n: usize, l: f64 }

fn cdiv(a: I, b: I) -> I { -((-a).div_euclid(b)) }

fn cert(n: i64, r: i64, sab: i64) -> Res {
    let sp: Vec<i64> = (1..=n).filter(|&i| i != r).collect();
    let g0 = complement(&sp, n);
    let mut res = Res { exc: vec![], fam: vec![], deg: false, w0: 0, tmax: 0, g0n: g0.len(), l: 0.0 };
    let l = match longest(&g0) { None => { res.deg = true; return res; } Some(l) => l };
    res.l = l.f();
    let nn = n as I;
    let w0 = (4 * (nn + 2) * l.q).div_euclid(nn * (nn - 4) * l.p) + 1;
    let w0s = std::cmp::max(w0 / sab as I, 1);
    res.w0 = w0 as i64;
    let mut w1 = n + 1;
    while (w1 as I) < w0s {
        let g1 = restrict(&g0, w1, n, false);
        match longest(&g1) {
            None => { res.fam.push(w1); }
            Some(lp) => {
                let t = cdiv(2 * lp.q, nn * lp.p);
                let ts = cdiv(t, sab as I);
                if t as i64 > res.tmax { res.tmax = t as i64; }
                let mut w2 = w1 + 1;
                while (w2 as I) < ts {
                    if restrict(&g1, w2, n, true).is_empty() { res.exc.push((w1, w2)); }
                    w2 += 1;
                }
            }
        }
        w1 += 1;
    }
    res
}

// ---- exact ML by sum-candidates t = k/(vi+vj) ----
fn dmin(sp: &[i64], k: i64, m: i64) -> i64 {
    let mut d = m;
    for &v in sp {
        let x = ((v as i128 * k as i128) % m as i128) as i64;
        let y = std::cmp::min(x, m - x);
        if y < d { d = y; }
    }
    d
}
// returns (num,den) max over candidates
fn ml(sp: &[i64]) -> (i64, i64) {
    let mut best = (0i64, 1i64);
    for i in 0..sp.len() {
        for j in i..sp.len() {
            let m = sp[i] + sp[j];
            for k in 1..=(m / 2) {
                let d = dmin(sp, k, m);
                // d/m > best.0/best.1 ?
                if (d as i128) * (best.1 as i128) > (best.0 as i128) * (m as i128) { best = (d, m); }
            }
        }
    }
    best
}
fn ml_ge(sp: &[i64], n: i64) -> bool { // ML >= 1/n by early exit
    for i in 0..sp.len() {
        for j in i..sp.len() {
            let m = sp[i] + sp[j];
            for k in 1..=(m / 2) {
                if dmin(sp, k, m) * n >= m { return true; }
            }
        }
    }
    false
}
fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn red(x: (i64, i64)) -> (i64, i64) { let g = gcd(x.0, x.1); (x.0 / g, x.1 / g) }

// ---- brute: left-endpoint candidates, direct ||v t|| checks, i64 ----
static STRICT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
fn good_at(p: i64, q: i64, v: i64, n: i64) -> bool {
    let x = ((v as i128 * p as i128) % q as i128) as i64;
    let d = std::cmp::min(x, q - x);
    if STRICT.load(std::sync::atomic::Ordering::Relaxed) { d * n > q } else { d * n >= q }
}
struct Brute { a0: Vec<(i64, i64)>, e: Vec<Vec<(i64, i64)>>, n: i64, w_lo: i64 }
fn brute_prep(n: i64, r: i64, wmax: i64) -> Brute {
    let sp: Vec<i64> = (1..=n).filter(|&i| i != r).collect();
    let all_good = |p: i64, q: i64| sp.iter().all(|&v| good_at(p, q, v, n));
    let mut a0 = Vec::new();
    for &i in &sp {
        let mut k = 0i64;
        while 2 * (k * n + 1) <= i * n {
            if all_good(k * n + 1, i * n) { a0.push((k * n + 1, i * n)); }
            k += 1;
        }
    }
    let mut e = Vec::new();
    for w in (n + 1)..=wmax {
        let mut v = Vec::new();
        let mut k = 0i64;
        while 2 * (k * n + 1) <= w * n {
            if all_good(k * n + 1, w * n) { v.push((k * n + 1, w * n)); }
            k += 1;
        }
        e.push(v);
    }
    Brute { a0, e, n, w_lo: n + 1 }
}
fn brute_ok(b: &Brute, w1: i64, w2: i64) -> bool {
    let n = b.n;
    for &(p, q) in &b.a0 { if good_at(p, q, w1, n) && good_at(p, q, w2, n) { return true; } }
    for &(p, q) in &b.e[(w1 - b.w_lo) as usize] { if good_at(p, q, w2, n) { return true; } }
    for &(p, q) in &b.e[(w2 - b.w_lo) as usize] { if good_at(p, q, w1, n) { return true; } }
    false
}

fn rmax(n: i64, rm: &str) -> i64 {
    if rm == "h" { n / 2 } else if let Some(k) = rm.strip_prefix('m') { n - k.parse::<i64>().unwrap() } else { rm.parse().unwrap() }
}
fn pr(x: (i64, i64)) -> String { let y = red(x); format!("{}/{}", y.0, y.1) }

fn main() {
    let a: Vec<String> = env::args().collect();
    if env::var("STRICT").is_ok() { STRICT.store(true, std::sync::atomic::Ordering::Relaxed); }
    match a[1].as_str() {
        "cert" => {
            let (n0, n1): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let sab: i64 = if a.len() > 5 { a[5].parse().unwrap() } else { 1 };
            let mut tot = 0usize; let mut totfam = 0; let mut pairs = 0u64; let mut maxw0 = 0; let mut maxt = 0; let mut deg = 0;
            for n in n0..=n1 {
                let mut cnt = 0usize; let mut rs = Vec::new(); let mut fams = 0;
                for r in 1..=rmax(n, &a[4]) {
                    let x = cert(n, r, sab);
                    pairs += 1;
                    if x.deg { deg += 1; println!("DEG N={} r={}", n, r); continue; }
                    maxw0 = maxw0.max(x.w0); maxt = maxt.max(x.tmax);
                    if !x.exc.is_empty() || !x.fam.is_empty() { rs.push(r); }
                    cnt += x.exc.len(); fams += x.fam.len();
                    if n <= 20 || a.len() > 6 { for (w1, w2) in &x.exc { println!("EXC N={} r={} w1={} w2={}", n, r, w1, w2); } for w in &x.fam { println!("FAM N={} r={} w1={}", n, r, w); } }
                }
                tot += cnt; totfam += fams;
                println!("N={} exceptions={} fam_w1={} r_with_exc={:?}", n, cnt, fams, rs);
            }
            println!("SUMMARY N={}..{} R={} sab={} (N,r)pairs={} exceptions={} fam_w1={} deg={} maxW0={} maxT={}", n0, n1, a[4], sab, pairs, tot, totfam, deg, maxw0, maxt);
        }
        "thr" => {
            let (n0, n1): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let (mut bw, mut bt) = ((0, 0, 0), (0, 0, 0));
            for n in n0..=n1 { for r in 1..=rmax(n, &a[4]) { let x = cert(n, r, 1); if x.deg { continue; } if x.w0 > bw.0 { bw = (x.w0, n, r); } if x.tmax > bt.0 { bt = (x.tmax, n, r); } } }
            println!("max W0={} at N={} r={}; max T={} at N={} r={}", bw.0, bw.1, bw.2, bt.0, bt.1, bt.2);
        }
        "one" => {
            let (n, r): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let sp: Vec<i64> = (1..=n).filter(|&i| i != r).collect();
            let g0 = complement(&sp, n);
            println!("G0 pieces ({}):", g0.len());
            for p in &g0 { println!("  [{}/{}, {}/{}] len={:.6e} ({:.6}..{:.6})", p.a.p, p.a.q, p.b.p, p.b.q, p.b.sub(&p.a).f(), p.a.f(), p.b.f()); }
            let x = cert(n, r, 1);
            println!("l={:.6e} W0={} tmax={} exceptions={} fam={:?}", x.l, x.w0, x.tmax, x.exc.len(), x.fam);
            for (w1, w2) in &x.exc {
                let mut v = sp.clone(); v.push(*w1); v.push(*w2);
                let m = ml(&v);
                println!("EXC ({},{}) ML={} = {:.6}  1/N={:.6}", w1, w2, pr(m), m.0 as f64 / m.1 as f64, 1.0 / n as f64);
            }
        }
        "brute" | "xcheck" => {
            let (n0, n1): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let wmax: i64 = a[5].parse().unwrap();
            let x = a[1] == "xcheck";
            let mut tb = 0u64; let mut tc = 0u64; let mut mism = 0u64; let mut sets = 0u64;
            for n in n0..=n1 {
                let mut nb = 0u64;
                for r in 1..=rmax(n, &a[4]) {
                    let b = brute_prep(n, r, wmax);
                    let mut bexc: Vec<(i64, i64)> = Vec::new();
                    for w1 in (n + 1)..=wmax { for w2 in (w1 + 1)..=wmax { sets += 1; if !brute_ok(&b, w1, w2) { bexc.push((w1, w2)); } } }
                    nb += bexc.len() as u64;
                    if x {
                        let c = cert(n, r, 1);
                        if !c.fam.is_empty() || c.deg { continue; }
                        let mut cexc: Vec<(i64, i64)> = c.exc.iter().cloned().filter(|e| e.1 <= wmax).collect();
                        cexc.sort(); bexc.sort();
                        if cexc != bexc { mism += 1; println!("MISMATCH N={} r={} cert={} brute={}", n, r, cexc.len(), bexc.len()); }
                        // exceptions of cert must also lie in w2<=wmax restricted set only; report if cert has any with w2>wmax
                        tc += c.exc.len() as u64;
                    }
                    if n <= 20 && a.len() > 6 { for (w1, w2) in &bexc { println!("BEXC N={} r={} {} {}", n, r, w1, w2); } }
                }
                tb += nb;
                println!("N={} brute_exceptions={}", n, nb);
            }
            println!("SUMMARY {} N={}..{} R={} wmax={} sets={} brute_exc={} cert_exc_total={} mismatches={}", a[1], n0, n1, a[4], wmax, sets, tb, tc, mism);
        }
        "mlscan" => {
            let (n, r): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let wmax: i64 = a[4].parse().unwrap();
            let b = brute_prep(n, r, wmax);
            let sp: Vec<i64> = (1..=n).filter(|&i| i != r).collect();
            let (mut mm, mut bad, mut tot) = (0, 0, 0);
            for w1 in (n + 1)..=wmax { for w2 in (w1 + 1)..=wmax {
                let mut v = sp.clone(); v.push(w1); v.push(w2);
                let d1 = ml_ge(&v, n); let d2 = brute_ok(&b, w1, w2);
                tot += 1; if !d2 { bad += 1; } if d1 != d2 { mm += 1; println!("MLMISMATCH {} {}", w1, w2); }
            } }
            println!("SUMMARY mlscan N={} r={} wmax={} sets={} failing={} mismatches={}", n, r, wmax, tot, bad, mm);
        }
        "ctl" => {
            let mut fails = 0;
            for n in 1..=13i64 { let v: Vec<i64> = (1..=n).collect(); let m = red(ml(&v)); if m != (1, n + 1) { fails += 1; println!("CTL FAIL [{}] = {}/{}", n, m.0, m.1); } }
            let mut v: Vec<i64> = (1..=20).filter(|&i| i != 6).collect(); v.push(29); v.push(31);
            let m = red(ml(&v)); println!("N=20 r=6 {{29,31}} ML={}/{}", m.0, m.1); if m != (2, 41) { fails += 1; }
            let mut v: Vec<i64> = (1..=21).filter(|&i| i != 6).collect(); v.push(29); v.push(31);
            let m = red(ml(&v)); println!("N=21 r=6 {{29,31}} ML={}/{} (>=1/21 needed)", m.0, m.1); if (m.0 as i128) * 21 < m.1 as i128 { fails += 1; }
            let mut v: Vec<i64> = (1..=13).filter(|&i| i != 6).collect(); v.push(69);
            let m = red(ml(&v)); println!("N=13 r=6 {{69}} ML={}/{}", m.0, m.1); if m != (3, 40) { fails += 1; }
            let mut v: Vec<i64> = (1..=49).filter(|&i| i != 45).collect(); v.push(90); v.push(731);
            let m = red(ml(&v)); println!("N=49 r=45 {{90,731}} ML={}/{} vs 1/49", m.0, m.1);
            println!("CTL fails={}", fails);
        }
        _ => println!("unknown mode"),
    }
}
