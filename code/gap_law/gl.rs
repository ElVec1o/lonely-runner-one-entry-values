// gl.rs.  Exact integer arithmetic only.  Build: rustc -O gl.rs
// ML(v) = max_t min_k ||t v_k||.  Local maxima of the min lie at t = n/S, S = v_i+v_j (i<=j), so ML is a finite max.
// modes:
//   gl ml v1 v2 ...                      exact ML, reduced, and every maximising time n/S (reduced, t in (0,1/2])
//   gl scan N NUM DEN VMAX M             all primitive N-subsets of [1,VMAX] with ML <= NUM/DEN  (exhaustive in the box)
//        necessary-condition pool: times a/m, m<=M; branch on the uncovered time with fewest allowed candidates,
//        forbidding earlier siblings (each set found once); when the pool is covered, exact ML of the partial set
//        gives a witness time and the branching continues on it (so the search is exact, the pool is only a speed-up).
use std::env;
const TW: usize = 24; // time-pool words (<=1536 times)
const XW: usize = 16; // speed words (VMAX <= 1023)

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
#[inline] fn fold(r: u64, m: u64) -> u64 { if 2 * r > m { m - r } else { r } }

// exact ML: returns (num, den) unreduced best, and optionally collects witness times (n,S) with value > tn/td
fn ml_exact(v: &[u64], tau: Option<(u64, u64)>, wit: &mut Vec<(u64, u64)>, wcap: usize) -> (u64, u64) {
    let (mut bn, mut bd) = (0u64, 1u64);
    let k = v.len();
    for i in 0..k { for j in i..k {
        let s = v[i] + v[j];
        for n in 1..=(s / 2) {
            let mut mn = u64::MAX;
            for &x in v { let f = fold((n * x) % s, s); if f < mn { mn = f; if mn * bd <= bn * s && tau.is_none() { break; } } }
            if mn * bd > bn * s { bn = mn; bd = s; }
            if let Some((tn, td)) = tau { if td * mn > tn * s && wit.len() < wcap { let g = gcd(n, s); wit.push((n / g, s / g)); } }
        }
    }}
    (bn, bd)
}

struct Ctx {
    n: usize, num: u64, den: u64, vmax: usize,
    nt: usize, times: Vec<(u64, u64)>,
    mask: Vec<[u64; TW]>,  // mask[x]: pool times covered by x
    cand: Vec<[u64; XW]>,  // cand[t]: speeds covering time t
    nodes: u64, lazy: u64, exact_full: u64, sols: Vec<(Vec<u64>, u64, u64)>, viol: u64,
}
#[inline] fn covers(c: &Ctx, x: u64, a: u64, m: u64) -> bool { c.den * fold((a * x) % m, m) <= c.num * m }

fn lazy(c: &mut Ctx, s: &mut Vec<u64>, allowed: &mut [u64; XW]) {
    c.lazy += 1;
    let mut wit: Vec<(u64, u64)> = Vec::new();
    let (bn, bd) = ml_exact(s, Some((c.num, c.den)), &mut wit, 400);
    if s.len() == c.n { c.exact_full += 1; }
    if c.den * bn <= c.num * bd {
        if s.len() < c.n { c.viol += 1; println!("SUBSET-WITH-ML<=TAU (size {}) {:?} ML={}/{}", s.len(), s, bn, bd); return; }
        let g0 = s.iter().fold(0, |g, &x| gcd(g, x));
        if g0 == 1 { let g = gcd(bn, bd); let mut t = s.clone(); t.sort(); c.sols.push((t, bn / g, bd / g)); }
        return;
    }
    if s.len() == c.n { return; }
    wit.sort(); wit.dedup();
    // choose the witness time with fewest allowed covering speeds
    let mut best: Vec<u64> = Vec::new(); let mut bc = usize::MAX;
    for &(a, m) in wit.iter() {
        let mut l: Vec<u64> = Vec::new();
        for x in 1..=(c.vmax as u64) { if allowed[(x >> 6) as usize] >> (x & 63) & 1 == 1 && covers(c, x, a, m) { l.push(x); if l.len() >= bc { break; } } }
        if l.len() < bc { bc = l.len(); best = l; if bc == 0 { return; } }
    }
    let saved = *allowed;
    for &x in best.iter() {
        allowed[(x >> 6) as usize] &= !(1u64 << (x & 63));
        s.push(x); let mut al = *allowed; lazy(c, s, &mut al); s.pop();
    }
    *allowed = saved;
}

fn dfs(c: &mut Ctx, s: &mut Vec<u64>, unc: &[u64; TW], allowed: &mut [u64; XW]) {
    c.nodes += 1;
    if c.nodes & ((1 << 27) - 1) == 0 { eprintln!("nodes {} lazy {} sols {} top {:?}", c.nodes, c.lazy, c.sols.len(), &s[..s.len().min(4)]); }
    let tw = (c.nt + 63) / 64; let xw = c.vmax / 64 + 1;
    if unc[..tw].iter().all(|&w| w == 0) { let mut al = *allowed; lazy(c, s, &mut al); return; }
    let r = c.n - s.len();
    if r == 0 { return; }
    if r == 1 {
        let mut inter = *allowed;
        for w in 0..tw { let mut b = unc[w]; while b != 0 { let t = w * 64 + b.trailing_zeros() as usize; b &= b - 1;
            let mut any = 0u64; for i in 0..xw { inter[i] &= c.cand[t][i]; any |= inter[i]; } if any == 0 { return; } } }
        for i in 0..xw { let mut b = inter[i]; while b != 0 { let x = (i * 64 + b.trailing_zeros() as usize) as u64; b &= b - 1;
            s.push(x); let mut al = *allowed; lazy(c, s, &mut al); s.pop(); } }
        return;
    }
    let mut bt = usize::MAX; let mut bc = u32::MAX;
    for w in 0..tw { let mut b = unc[w]; while b != 0 { let t = w * 64 + b.trailing_zeros() as usize; b &= b - 1;
        let mut cnt = 0u32; for i in 0..xw { cnt += (c.cand[t][i] & allowed[i]).count_ones(); }
        if cnt == 0 { return; }
        if cnt < bc { bc = cnt; bt = t; } } }
    let saved = *allowed;
    for i in 0..xw { let mut b = c.cand[bt][i] & saved[i]; while b != 0 { let x = i * 64 + b.trailing_zeros() as usize; b &= b - 1;
        allowed[i] &= !(1u64 << (x & 63));
        let mut u2 = *unc; for w in 0..tw { u2[w] &= !c.mask[x][w]; }
        s.push(x as u64); let mut al = *allowed; dfs(c, s, &u2, &mut al); s.pop(); } }
    *allowed = saved;
}

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() >= 3 && a[1] == "ml" {
        let v: Vec<u64> = a[2..].iter().map(|x| x.parse().unwrap()).collect();
        let mut w = Vec::new();
        let (bn, bd) = ml_exact(&v, None, &mut w, 0);
        let g = gcd(bn, bd);
        // maximising times
        let mut ts: Vec<(u64, u64)> = Vec::new();
        for i in 0..v.len() { for j in i..v.len() { let s = v[i] + v[j]; for n in 1..=(s / 2) {
            let mn = v.iter().map(|&x| fold((n * x) % s, s)).min().unwrap();
            if mn * bd == bn * s { let h = gcd(n, s); ts.push((n / h, s / h)); } } } }
        ts.sort(); ts.dedup();
        let tt: Vec<String> = ts.iter().map(|&(n, s)| format!("{}/{}", n, s)).collect();
        println!("ML {:?} = {}/{}  times: {}", v, bn / g, bd / g, tt.join(" "));
        return;
    }
    if a.len() >= 7 && a[1] == "scan" {
        let n: usize = a[2].parse().unwrap(); let num: u64 = a[3].parse().unwrap(); let den: u64 = a[4].parse().unwrap();
        let vmax: usize = a[5].parse().unwrap(); let m: u64 = a[6].parse().unwrap();
        assert!(vmax <= 64 * XW - 1);
        let mut times = Vec::new();
        for mm in 2..=m { for aa in 1..=(mm / 2) { if gcd(aa, mm) == 1 { times.push((aa, mm)); } } }
        let nt = times.len(); assert!(nt <= 64 * TW, "pool too large: {}", nt);
        let mut c = Ctx { n, num, den, vmax, nt, times, mask: vec![[0; TW]; vmax + 1], cand: vec![[0; XW]; nt], nodes: 0, lazy: 0, exact_full: 0, sols: Vec::new(), viol: 0 };
        for t in 0..nt { let (aa, mm) = c.times[t]; for x in 1..=vmax { if covers(&c, x as u64, aa, mm) { c.mask[x][t / 64] |= 1 << (t % 64); c.cand[t][x / 64] |= 1 << (x % 64); } } }
        let mut unc = [0u64; TW]; for t in 0..nt { unc[t / 64] |= 1 << (t % 64); }
        let mut allowed = [0u64; XW]; for x in 1..=vmax { allowed[x / 64] |= 1 << (x % 64); }
        let mut s = Vec::new();
        dfs(&mut c, &mut s, &unc, &mut allowed);
        c.sols.sort_by(|p, q| (p.1 * q.2).cmp(&(q.1 * p.2)).then(p.0.cmp(&q.0)));
        for (v, bn, bd) in c.sols.iter() { println!("SOL {}/{} {:?}", bn, bd, v); }
        println!("DONE N={} tau={}/{} VMAX={} M={} pool={} nodes={} lazy={} exactN={} sols={} subsetviol={} RESOLVED", n, num, den, vmax, m, nt, c.nodes, c.lazy, c.exact_full, c.sols.len(), c.viol);
        return;
    }
    eprintln!("usage: gl ml v...   |   gl scan N NUM DEN VMAX M");
}
