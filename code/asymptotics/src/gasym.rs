// gasym.rs.  rustc -O gasym.rs
// N = number of speeds, A = N+1, r in (N/2,N], s = A-r, beta = least b >= s with gcd(b,r)=1, m = floor(beta/s)+1,
// e = m s - beta in [1,s].  Family value m/(m r + beta) = m/(mA - e) = 1/(A - e/m).   G(N) = 1/(A - mu(N)), mu = min_r e/m <= 1/2.
// Pruning: m >= 3 (needed for e/m < 1/2) forces every b in [s,2s-1] non-coprime to r, hence every PRIME in [s,2s-1] divides r,
// hence Pi_s = prod of primes in [s,2s-1] <= r <= N.  Only s = 1 (r = N, value 1/2) and s >= 2 with Pi_s <= N are scanned; every
// other s has m = 2, e/m = (2s-beta)/2 >= 1/2 and cannot lower mu below 1/2.
//   gasym run NMAX CHUNK OUTDIR   : chunk files OUTDIR/cNNN.tsv (atomic rename, resume = skip existing); lines: N s r beta m e fmask smask
//   gasym val NLO NHI             : prints "N num den" = G(N) reduced
//   gasym agg OUTDIR NMAX         : tables
use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::Write;
use std::time::Instant;

fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }

fn cand_list(nmax: u64) -> Vec<u64> {
    let lim = 60000usize;
    let mut comp = vec![false; lim + 1];
    let mut th = vec![0f64; lim + 1]; // theta prefix
    for i in 2..=lim {
        if !comp[i] { let mut j = i * i; while j <= lim { comp[j] = true; j += i; } }
        th[i] = th[i - 1] + if !comp[i] { (i as f64).ln() } else { 0.0 };
    }
    let lnn = (nmax as f64).ln() + 1e-6;
    let mut v = vec![];
    for s in 2..=(lim / 2 - 1) { if th[2 * s - 1] - th[s - 1] <= lnn { v.push(s as u64); } }
    v
}

#[derive(Clone, Copy)]
struct Rec { n: u64, s: u64, r: u64, beta: u64, m: u64, e: u64, fmask: u64, smask: u64 }

fn eval(n: u64, cand: &[u64]) -> Rec {
    let a = n + 1;
    let mut best = Rec { n, s: 1, r: n, beta: 1, m: 2, e: 1, fmask: 0, smask: 0 };
    for &s in cand {
        if 2 * s > a { break; }
        let r = a - s;
        let mut b = s;
        while gcd(b, r) != 1 { b += 1; }
        let m = b / s + 1;
        let e = m * s - b;
        if b >= 2 * s && s < 64 { best.fmask |= 1u64 << s; }
        if 2 * e < m && s < 64 { best.smask |= 1u64 << s; }
        if e * best.m < best.e * m { best.s = s; best.r = r; best.beta = b; best.m = m; best.e = e; }
    }
    best
}

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() >= 5 && a[1] == "run" {
        let nmax: u64 = a[2].parse().unwrap(); let chunk: u64 = a[3].parse().unwrap(); let dir = &a[4];
        fs::create_dir_all(dir).unwrap();
        let cand = cand_list(nmax);
        println!("candidate s (Pi_s <= {}): {:?}", nmax, cand);
        assert!(cand.iter().all(|&s| s < 64));
        let t0 = Instant::now();
        let nch = (nmax + chunk) / chunk;
        for k in 0..nch {
            let lo = std::cmp::max(2, k * chunk); let hi = std::cmp::min((k + 1) * chunk - 1, nmax);
            if lo > hi { continue; }
            let fin = format!("{}/c{:03}.tsv", dir, k);
            if fs::metadata(&fin).is_ok() { println!("chunk {} exists, skip", k); continue; }
            let tmp = format!("{}.tmp", fin);
            let mut f = std::io::BufWriter::new(fs::File::create(&tmp).unwrap());
            for n in lo..=hi { let x = eval(n, &cand);
                writeln!(f, "{} {} {} {} {} {} {} {}", x.n, x.s, x.r, x.beta, x.m, x.e, x.fmask, x.smask).unwrap(); }
            f.flush().unwrap(); drop(f); fs::rename(&tmp, &fin).unwrap();
            let el = t0.elapsed().as_secs_f64(); let done = (k + 1) as f64 / nch as f64;
            println!("chunk {}/{} N={}..{} done, elapsed {:.1}s, ETA {:.1}s", k + 1, nch, lo, hi, el, el * (1.0 - done) / done);
        }
        println!("DONE run NMAX={}", nmax);
        return;
    }
    if a.len() >= 4 && a[1] == "val" {
        let lo: u64 = a[2].parse().unwrap(); let hi: u64 = a[3].parse().unwrap();
        let cand = cand_list(hi);
        for n in lo..=hi { let x = eval(n, &cand); let num = x.m; let den = x.m * (n + 1) - x.e; let g = gcd(num, den);
            println!("{} {} {}", n, num / g, den / g); }
        return;
    }
    if a.len() >= 4 && a[1] == "agg" {
        let dir = &a[2]; let nmax: u64 = a[3].parse().unwrap();
        let chunk_files: Vec<_> = { let mut v: Vec<_> = fs::read_dir(dir).unwrap().map(|x| x.unwrap().path()).filter(|p| p.extension().map_or(false, |e| e == "tsv")).collect(); v.sort(); v };
        // block stats
        #[derive(Clone)] struct B { n: u64, ne: u64, minv: f64, minv_n: u64, minvl: f64, minvl_n: u64, maxv: f64, maxv_n: u64, forced: u64 }
        let mut blocks: Vec<B> = vec![B { n: 0, ne: 0, minv: 1e18, minv_n: 0, minvl: 1e18, minvl_n: 0, maxv: 0.0, maxv_n: 0, forced: 0 }; 22];
        let mut ws: HashMap<u64, u64> = HashMap::new(); let mut wt: HashMap<(u64, u64, u64), u64> = HashMap::new(); let mut wm: HashMap<u64, u64> = HashMap::new();
        let mut min_win = [0u64; 64]; let mut min_str = [0u64; 64]; let mut min_for = [0u64; 64];
        let mut cnt_for = [0u64; 64]; let mut cnt_str = [0u64; 64];
        let (mut viol, mut forced_not_strict, mut total, mut tie_half_nonS1) = (0u64, 0u64, 0u64, 0u64);
        let mut fns_by_s: HashMap<u64, u64> = HashMap::new();
        let pmod = [(2u64, 6u64), (3, 30), (4, 70), (5, 210)];
        let mut cong_mis = [0u64; 4]; let mut cong_eq = [0u64; 4];
        let mut rec_low = 1e18f64; let mut recs: Vec<(u64, f64, u64, u64, u64)> = vec![];
        let mut nmax_seen = 0;
        for p in &chunk_files {
            let txt = fs::read_to_string(p).unwrap();
            for line in txt.lines() {
                let v: Vec<u64> = line.split(' ').map(|x| x.parse().unwrap()).collect();
                let (n, s, r, beta, m, e, fm, sm) = (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
                if n > nmax { continue; }
                nmax_seen = n; total += 1;
                let aa = (n + 1) as f64;
                let val = (n as f64) * (n as f64) * (e as f64) / (aa * ((m as f64) * aa - e as f64));
                let lg = (n as f64).ln(); let vl = val * lg;
                let strict = 2 * e < m;
                let k = 63 - n.leading_zeros() as usize;
                let b = &mut blocks[k]; b.n += 1; if strict { b.ne += 1; } if fm != 0 { b.forced += 1; }
                if val < b.minv { b.minv = val; b.minv_n = n; } if val > b.maxv { b.maxv = val; b.maxv_n = n; }
                if vl < b.minvl { b.minvl = vl; b.minvl_n = n; }
                if n >= 8 && vl < rec_low { rec_low = vl; recs.push((n, vl, s, m, beta)); }
                if strict { *ws.entry(s).or_insert(0) += 1; *wt.entry((s, m, beta)).or_insert(0) += 1; *wm.entry(m).or_insert(0) += 1;
                    if min_win[s as usize] == 0 { min_win[s as usize] = n; } }
                else if s != 1 { tie_half_nonS1 += 1; }
                for q in 2..64usize { if (sm >> q) & 1 == 1 { cnt_str[q] += 1; if min_str[q] == 0 { min_str[q] = n; } }
                    if (fm >> q) & 1 == 1 { cnt_for[q] += 1; if min_for[q] == 0 { min_for[q] = n; } } }
                if strict && fm == 0 { viol += 1; }
                if fm != 0 && !strict { forced_not_strict += 1; let ls = fm.trailing_zeros() as u64; *fns_by_s.entry(ls).or_insert(0) += 1; }
                for (i, &(s0, pp)) in pmod.iter().enumerate() {
                    let rr = n + 1 - s0; let pred = 2 * s0 <= n + 1 && rr % pp == 0; let act = (fm >> s0) & 1 == 1;
                    if pred { cong_eq[i] += 1; } if pred != act { cong_mis[i] += 1; }
                }
            }
        }
        println!("AGG records={} last N={}", total, nmax_seen);
        println!("\n== dyadic blocks: density of {{G(N)=2/(2N+1)}}, N^2(G-1/A), N^2 log N (G-1/A) ==");
        println!("block            n    #strict(G<2/(2N+1))  density(G=2/(2N+1))  density(forcing any s)  max N^2(G-1/A)@N   min N^2(G-1/A)@N   min logN*N^2(G-1/A)@N");
        for k in 1..22 { let b = &blocks[k]; if b.n == 0 { continue; }
            println!("[2^{:>2},2^{:>2}) {:>8} {:>8} {:>22.5} {:>22.5} {:>12.6}@{:<8} {:>12.6}@{:<8} {:>12.6}@{}", k, k + 1, b.n, b.ne, 1.0 - b.ne as f64 / b.n as f64, 1.0 - b.forced as f64 / b.n as f64, b.maxv, b.maxv_n, b.minv, b.minv_n, b.minvl, b.minvl_n); }
        let tn: u64 = blocks.iter().map(|b| b.n).sum(); let te: u64 = blocks.iter().map(|b| b.ne).sum(); let tf: u64 = blocks.iter().map(|b| b.forced).sum();
        println!("TOTAL N=2..{}: n={} strict={} density(G=2/(2N+1))={:.5}  density(no forcing s)={:.5}", nmax_seen, tn, te, 1.0 - te as f64 / tn as f64, 1.0 - tf as f64 / tn as f64);
        println!("\n== winner s among strict N (G<2/(2N+1)) ==");
        let mut v: Vec<_> = ws.iter().collect(); v.sort(); for (s, c) in v { println!("s={:>3} wins {:>8}", s, c); }
        println!("\n== winner m among strict N =="); let mut v: Vec<_> = wm.iter().collect(); v.sort(); for (s, c) in v { println!("m={:>3} wins {:>8}", s, c); }
        println!("\n== top winner (s,m,beta) =="); let mut v: Vec<_> = wt.iter().collect(); v.sort_by(|x, y| y.1.cmp(x.1)); for (t, c) in v.iter().take(20) { println!("(s,m,beta)=({},{},{}) wins {}", t.0, t.1, t.2, c); }
        println!("non-strict records with winner s != 1 (e/m = 1/2 ties, winner not s=1): {}", tie_half_nonS1);
        println!("\n== per s: minimal N with forcing(s) / strict(s) (2e<m at s) / s the winner; counts ==");
        for q in 2..40usize { if cnt_for[q] > 0 || cnt_str[q] > 0 { println!("s={:>2} minN_forcing={:>8} minN_strict={:>8} minN_winner={:>8} #forcing={:>7} #strict={:>7} dens_forcing={:.6}", q, min_for[q], min_str[q], min_win[q], cnt_for[q], cnt_str[q], cnt_for[q] as f64 / total as f64); } }
        println!("\n== forcing criterion tests ==");
        println!("strict(G<2/(2N+1)) but no forcing s (must be 0, math: m>=3 needs beta>=2s): {}", viol);
        println!("forcing s exists but G=2/(2N+1) (forcing not sufficient): {}  by lowest forcing s: {:?}", forced_not_strict, { let mut v: Vec<_> = fns_by_s.iter().collect(); v.sort(); v });
        for (i, &(s0, pp)) in pmod.iter().enumerate() { println!("congruence s={} (P={}| N+1-s, 2s<=N+1): #pred={} mismatches vs exact forcing test={}", s0, pp, cong_eq[i], cong_mis[i]); }
        println!("\n== record lows of N^2 log N (G-1/A), N>=8 ==");
        for (n, vl, s, m, beta) in &recs { println!("N={:>8} value={:.6} winner s={} m={} beta={}", n, vl, s, m, beta); }
        return;
    }
    eprintln!("usage: gasym run NMAX CHUNK OUTDIR | val NLO NHI | agg OUTDIR NMAX");
}
