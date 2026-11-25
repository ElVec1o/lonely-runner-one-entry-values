// n02: exact engine for N0(2).
// Objects: tau = p/q. Good set of speed set S: G(S) = {t in [0,1/2] : ||v t|| >= tau for all v in S}, a finite union of CLOSED pieces.
// Representation: Vec<(Fr,Fr)> of closed pieces [lo,hi], lo<=hi (point pieces allowed).
// Single-speed primitive next_good(t,w): first good point >= t for speed w (one jump to the right end of the open band containing t).
// restrict(G,w): G intersect good(w) by walking each piece with next_good and the next band left end.
// ML exact: maximum over candidates t=k/(vi+vj) of min_v ||v t|| (local maxima of a min of tent functions are crossings of an increasing and a decreasing branch).
use std::env;
type I = i128;
#[derive(Clone, Copy, Debug)]
struct Fr { n: I, d: I }
fn fr(n: I, d: I) -> Fr { Fr { n, d } }
fn le(a: Fr, b: Fr) -> bool { a.n * b.d <= b.n * a.d }
fn lt(a: Fr, b: Fr) -> bool { a.n * b.d < b.n * a.d }
fn gcd(a: I, b: I) -> I { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn red(a: Fr) -> Fr { let g = gcd(a.n, a.d).max(1); fr(a.n / g, a.d / g) }
fn cdiv(a: I, b: I) -> I { -((-a).div_euclid(b)) } // b>0
fn fdiv(a: I, b: I) -> I { a.div_euclid(b) }
fn show(f: Fr) -> String { let g = red(f); format!("{}/{}", g.n, g.d) }
fn minf(a: Fr, b: Fr) -> Fr { if le(a, b) { a } else { b } }
fn len(a: Fr, b: Fr) -> Fr { fr(b.n * a.d - a.n * b.d, a.d * b.d) }

#[derive(Clone, Copy)]
struct Tau { p: I, q: I }

// first good point >= t for speed w (tau=p/q)
fn next_good(t: Fr, w: I, tau: Tau) -> Fr {
    // t = a/b ; w t = wa/b ; m nearest integer
    let (a, b) = (t.n, t.d);
    let m = fdiv(2 * w * a + b, 2 * b);
    let dd = (w * a - m * b).abs();
    if dd * tau.q >= b * tau.p { return t; }
    fr(m * tau.q + tau.p, w * tau.q) // right end of band m
}
// G intersect good(w)
fn restrict(g: &[(Fr, Fr)], w: I, tau: Tau) -> Vec<(Fr, Fr)> {
    let mut out = Vec::new();
    for &(a, b) in g {
        let mut t = a;
        loop {
            let x = next_good(t, w, tau);
            if lt(b, x) { break; }
            // end of the good run containing x: left end of first band (mq-p)/(wq) >= x
            let m = cdiv(x.n * w * tau.q + x.d * tau.p, x.d * tau.q);
            let e = fr(m * tau.q - tau.p, w * tau.q);
            let hi = minf(e, b);
            out.push((x, hi));
            if le(b, e) { break; }
            t = fr(m * tau.q + tau.p, w * tau.q);
        }
    }
    out
}
fn full() -> Vec<(Fr, Fr)> { vec![(fr(0, 1), fr(1, 2))] }
fn pieces_of(vs: &[I], tau: Tau) -> Vec<(Fr, Fr)> {
    let mut g = full();
    for &v in vs { g = restrict(&g, v, tau); if g.is_empty() { break; } }
    g
}
// independent method: sort all open bands and take the complement in [0,1/2]
fn pieces_sweep(vs: &[I], tau: Tau) -> Vec<(Fr, Fr)> {
    let mut bands: Vec<(Fr, Fr)> = Vec::new();
    for &v in vs {
        let mut k = 0;
        loop {
            let lo = fr(k * tau.q - tau.p, v * tau.q);
            if 2 * lo.n >= lo.d { break; } // lo>=1/2
            bands.push((lo, fr(k * tau.q + tau.p, v * tau.q)));
            k += 1;
        }
    }
    bands.sort_by(|x, y| (x.0.n * y.0.d).cmp(&(y.0.n * x.0.d)));
    let mut out = Vec::new();
    let mut reach = fr(0, 1); // all of t<0 irrelevant; k=0 bands cover 0 so first piece starts at their max right end
    let mut started = false;
    for b in bands {
        if !started { reach = b.1; started = true; continue; }
        if le(reach, b.0) { out.push((reach, b.0)); }
        if lt(reach, b.1) { reach = b.1; }
    }
    if le(reach, fr(1, 2)) { out.push((reach, fr(1, 2))); }
    // clip: pieces starting at reach where the previous hi may exceed 1/2 are handled by the lo>=1/2 stop; clip hi to 1/2
    out.into_iter().map(|(a, b)| (a, minf(b, fr(1, 2)))).filter(|(a, b)| le(*a, *b)).collect()
}
fn has_good(g: &[(Fr, Fr)], w: I, tau: Tau) -> bool {
    for &(a, b) in g { if le(next_good(a, w, tau), b) { return true; } }
    false
}
fn longest(g: &[(Fr, Fr)]) -> Fr {
    let mut best = fr(0, 1);
    for &(a, b) in g { let l = len(a, b); if lt(best, l) { best = l; } }
    best
}
fn dist_int(v: I, k: I, s: I) -> I { let r = (v * k) % s; r.min(s - r) } // ||v k/s|| * s
fn ml_exact(vs: &[I]) -> Fr {
    let mut best = fr(0, 1);
    let mut u: Vec<I> = vs.to_vec(); u.sort(); u.dedup();
    for i in 0..u.len() { for j in i..u.len() {
        let s = u[i] + u[j];
        for k in 1..=(s / 2) {
            let mut m = I::MAX;
            for &v in &u { let d = dist_int(v, k, s); if d < m { m = d; if fr(m, s).n * best.d <= best.n * s && m * best.d <= best.n * s { break; } } }
            let c = fr(m, s);
            if lt(best, c) { best = c; }
        }
    } }
    // t=1/2 candidate
    let mut m = I::MAX; for &v in &u { let d = dist_int(v, 1, 2); m = m.min(d); }
    let c = fr(m, 2); if lt(best, c) { best = c; }
    red(best)
}
fn set_prime(n: I, r: I) -> Vec<I> { (1..=n).filter(|&i| i != r).collect() }

struct Res { nexc: u64, fam: u64, flags_g0: u64, maxw0: I, maxt: I, w1cnt: u64 }
// certify statement S(N,r): for all N<w1<w2 : ML([N]\{r} u {w1,w2}) >= 1/N. Prints exceptions. cap: abort if work too large.
fn cert_nr(n: I, r: I, print: bool, wcap: I) -> Option<Res> {
    let tau = Tau { p: 1, q: n };
    let g0 = pieces_of(&set_prime(n, r), tau);
    let l = longest(&g0);
    let mut res = Res { nexc: 0, fam: 0, flags_g0: 0, maxw0: 0, maxt: 0, w1cnt: 0 };
    if l.n == 0 { res.flags_g0 = 1; if print { println!("FLAG_G0 N={} r={} (no positive-length piece)", n, r); } return Some(res); }
    // M1: w1,w2 >= W0 good, W0 = floor(4(N+2)/(N(N-4) l)) + 1
    let sab: I = std::env::var("SABOTAGE").ok().and_then(|x| x.parse().ok()).unwrap_or(1);
    let w0 = (fdiv(4 * (n + 2) * l.d, n * (n - 4) * l.n) + 1) / sab;
    res.maxw0 = w0;
    if w0 > wcap { return None; }
    for w1 in (n + 1)..w0 {
        res.w1cnt += 1;
        let g1 = restrict(&g0, w1, tau);
        let l2 = longest(&g1);
        if g1.is_empty() { res.fam += 1; if print { println!("EXC_FAM_EMPTY N={} r={} w1={} (ML([N]\\{{r}}+{{w1}})<1/N, every w2)", n, r, w1); } continue; }
        if l2.n == 0 { res.fam += 1; if print { println!("EXC_FAM_POINTS N={} r={} w1={} (G1 finite point set: w2 multiple of the denominators fails)", n, r, w1); } continue; }
        // M2: w2 >= T good, T = ceil(2/(N l2))
        let t = cdiv(2 * l2.d, n * l2.n) / sab;
        if t > res.maxt { res.maxt = t; }
        if t > wcap * 20 { return None; }
        for w2 in (w1 + 1)..t {
            if !has_good(&g1, w2, tau) {
                res.nexc += 1;
                if print {
                    let mut vs = set_prime(n, r); vs.push(w1); vs.push(w2);
                    println!("EXC N={} r={} w1={} w2={} ML={}", n, r, w1, w2, show(ml_exact(&vs)));
                }
            }
        }
    }
    Some(res)
}
// k=1: for all w>N : ML([N]\{r} u {w}) >= 1/N
fn cert1_nr(n: I, r: I, print: bool) -> (u64, u64) {
    let tau = Tau { p: 1, q: n };
    let g0 = pieces_of(&set_prime(n, r), tau);
    let l = longest(&g0);
    if l.n == 0 { return (0, 1); }
    let t = cdiv(2 * l.d, n * l.n);
    let mut exc = 0u64;
    for w in (n + 1)..t {
        if !has_good(&g0, w, tau) {
            exc += 1;
            if print { let mut vs = set_prime(n, r); vs.push(w); println!("EXC1 N={} r={} w={} ML={}", n, r, w, show(ml_exact(&vs))); }
        }
    }
    (exc, 0)
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a.get(1).map(|s| s.as_str()).unwrap_or("");
    let p = |i: usize| -> I { a[i].parse::<I>().unwrap() };
    match mode {
        "ctl" => ctl(),
        "cert" => { // cert N0 N1 rmode(0: r<=N/2; k: r<=N-k) wcap
            let (n0, n1, rm, wcap) = (p(2), p(3), p(4), p(5));
            let (mut tot_exc, mut tot_nr, mut tot_skip) = (0u64, 0u64, 0u64);
            for n in n0..=n1 {
                let rmax = if rm == 0 { n / 2 } else { n - rm };
                let (mut e, mut fam, mut f0, mut mw, mut mt, mut skip, mut w1c) = (0u64, 0u64, 0u64, 0, 0, 0u64, 0u64);
                for r in 1..=rmax {
                    match cert_nr(n, r, true, wcap) {
                        Some(x) => { e += x.nexc; fam += x.fam; f0 += x.flags_g0; mw = mw.max(x.maxw0); mt = mt.max(x.maxt); w1c += x.w1cnt; }
                        None => { skip += 1; println!("SKIP N={} r={} (W0 or T over cap)", n, r); }
                    }
                }
                println!("N={} r<={} pairs={} exc_pairs={} fam={} flagG0={} skipped={} maxW0={} maxT={} w1tested={}", n, rmax, rmax, e, fam, f0, skip, mw, mt, w1c);
                tot_exc += e + fam + f0 as u64; tot_nr += rmax as u64; tot_skip += skip;
            }
            println!("TOTAL N={}..{} (N,r) pairs={} exceptions(+fam+flag)={} skipped(UNRESOLVED)={}", n0, n1, tot_nr, tot_exc, tot_skip);
        }
        "k1" => { // k1 N0 N1 : single added speed, r<=N/2
            let (n0, n1) = (p(2), p(3));
            for n in n0..=n1 {
                let (mut e, mut fl) = (0u64, 0u64);
                for r in 1..=(n / 2) { let (x, y) = cert1_nr(n, r, true); e += x; fl += y; }
                println!("K1 N={} r<={} exceptions={} flags={}", n, n / 2, e, fl);
            }
        }
        "brute" => { // brute N0 N1 wmax : every pair w1<w2<=wmax with G0 from sweep, exceptions listed (compare with cert)
            let (n0, n1, wmax) = (p(2), p(3), p(4));
            for n in n0..=n1 {
                let tau = Tau { p: 1, q: n };
                let mut cnt = 0u64;
                let mut sets = 0u64;
                for r in 1..=(n / 2) {
                    let g0 = pieces_sweep(&set_prime(n, r), tau);
                    for w1 in (n + 1)..=wmax {
                        let g1 = restrict(&g0, w1, tau);
                        for w2 in (w1 + 1)..=wmax {
                            sets += 1;
                            if !has_good(&g1, w2, tau) { cnt += 1; println!("BEXC N={} r={} w1={} w2={}", n, r, w1, w2); }
                        }
                    }
                }
                println!("BRUTE N={} r<={} wmax={} sets={} exceptions={}", n, n / 2, wmax, sets, cnt);
            }
        }
        "ml" => { // ml N r w1 [w2]
            let n = p(2); let r = p(3);
            let mut vs = set_prime(n, r); for i in 4..a.len() { vs.push(p(i)); }
            println!("ML = {}", show(ml_exact(&vs)));
        }
        _ => println!("modes: ctl | cert N0 N1 rmode wcap | k1 N0 N1 | brute N0 N1 wmax | ml N r w..."),
    }
}

// tiny deterministic LCG for the controls
struct Lcg(u64);
impl Lcg { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 } fn below(&mut self, m: u64) -> u64 { self.next() % m } }

fn ctl() {
    let mut fails = 0;
    let mut chk = |name: &str, ok: bool| { println!("CTL {} {}", name, if ok { "ok" } else { "FAIL" }); if !ok { fails += 1; } };
    let eq = |x: Fr, y: Fr| x.n * y.d == y.n * x.d;
    // known values
    let mut v = set_prime(8, 0); // [8]
    chk("[8]=1/9", eq(ml_exact(&v), fr(1, 9)));
    v = vec![1, 3, 4, 7]; chk("{1,3,4,7}=1/5", eq(ml_exact(&v), fr(1, 5)));
    v = set_prime(13, 6); v.push(69); chk("[13]-6+69=3/40", eq(ml_exact(&v), fr(3, 40)));
    v = set_prime(20, 6); v.push(29); v.push(31); chk("[20]-6+{29,31}=2/41", eq(ml_exact(&v), fr(2, 41)));
    v = set_prime(21, 6); v.push(29); v.push(31); chk("[21]-6+{29,31}>=1/21", !lt(ml_exact(&v), fr(1, 21)));
    v = set_prime(73, 0); v.retain(|&x| x != 70 && x != 72); v.push(140); v.push(144); chk("Zhang [73]-{70,72}+{140,144}=1/74", eq(ml_exact(&v), fr(1, 74)));
    // decision engine vs exact ML on random sets, at ML, ML+eps, ML-eps, with both piece methods
    let mut rng = Lcg(12345);
    let mut bad = 0u64; let mut tot = 0u64; let mut sweep_bad = 0u64;
    for it in 0..3000 {
        let nv = 2 + rng.below(8) as usize;
        let mx = 6 + rng.below(70);
        let mut vs: Vec<I> = (0..nv).map(|_| 1 + rng.below(mx) as I).collect();
        if it % 3 == 0 { vs.push(100 + rng.below(900) as I); }
        let ml = ml_exact(&vs);
        let eps = fr(ml.n * 1000 - 0, ml.d * 1000); let _ = eps;
        // tau = ml (decision true), tau slightly above (false), slightly below (true)
        let tau0 = Tau { p: ml.n, q: ml.d };
        let up = Tau { p: ml.n * 1000 + 1, q: ml.d * 1000 };
        let dn = Tau { p: ml.n * 1000 - 1, q: ml.d * 1000 };
        let a1 = !pieces_of(&vs, tau0).is_empty();
        let a2 = if ml.n * 2 == ml.d { true } else { pieces_of(&vs, up).is_empty() }; // tau>1/2 is outside the engine's domain
        let a3 = !pieces_of(&vs, dn).is_empty();
        tot += 1; if !(a1 && a2 && a3) { bad += 1; if bad<=6 { println!("MISMATCH vs={:?} ml={} a1={} a2={} a3={}", vs, show(ml), a1,a2,a3); } }
        // sweep method equality of pieces at tau = 1/7 and at ml
        for tt in [Tau { p: 1, q: 7 }, tau0] {
            let x = pieces_of(&vs, tt); let y = pieces_sweep(&vs, tt);
            let same = x.len() == y.len() && x.iter().zip(y.iter()).all(|(s, t)| eq(s.0, t.0) && eq(s.1, t.1));
            if !same { sweep_bad += 1; }
        }
    }
    println!("CTL random sets={} decision-vs-exactML mismatches={} fold-vs-sweep piece mismatches={}", tot, bad, sweep_bad);
    chk("decision vs exact ML (3 levels)", bad == 0);
    chk("fold vs sweep pieces", sweep_bad == 0);
    // negative control for the decision: ML(ml+eps) must be FALSE on at least some sets (instrument can say no)
    let g = pieces_of(&set_prime(13, 6).into_iter().chain([69]).collect::<Vec<_>>(), Tau { p: 1, q: 13 });
    chk("[13]-6+69 not >= 1/13", g.is_empty());
    let g = pieces_of(&set_prime(20, 6).into_iter().chain([29, 31]).collect::<Vec<_>>(), Tau { p: 1, q: 20 });
    chk("[20]-6+{29,31} not >= 1/20", g.is_empty());
    println!("CTL total failures {}", fails);
}
