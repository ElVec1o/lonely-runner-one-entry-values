// vf_steps.rs: mechanical re-derivation of the INTERMEDIATE claims of the proof (pass 2), not the final value.
//   S1  beta facts: gcd(beta,r)=1, s<=beta<=r+1, beta<=N, every b in [s,beta-1] has gcd(b,r)>1, s<=r.
//   S2  close set: with D=m r+beta, a r = -1 (mod D): {x in [1,D-1] : ||a x/D|| < m/D} = {k r, k r+beta : 1<=k<=m-1}  (exact set equality),
//       and ||a (m r)/D|| = m/D exactly; none of the close-set elements lies in [N]\{r}.
//   S3  blocker: for every unit u in [1,r-1] the representative x(u)=u (u>=s) or u+r (u<s) satisfies x<=N, x!=r, x>=beta, x = u mod r.
//   S4  key inequality (star): with tau = max(1/(N+1), m/(m r+beta)) = p/q:  m (q - r p) <= beta p   (exact integers), and 0 < q - r p.
//   S5  sharpness of S4: with tau0 = m/(m r+beta), equality m(q-rp) = beta p holds.
// usage: vf_steps NMIN NMAX MMIN MMAX
use std::env;
fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn main() {
    let a: Vec<String> = env::args().collect();
    let (nmin, nmax, mmin, mmax): (i128, i128, i128, i128) = (a[1].parse().unwrap(), a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap());
    let (mut inst, mut bad) = (0u64, 0u64);
    for n in nmin..=nmax { for r in (n / 2 + 1)..=n {
        let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; } beta += 1; while gcd(beta, r) != 1 { beta += 1; }
        let mut ok = true;
        // S1
        ok &= gcd(beta, r) == 1 && s <= beta && beta <= r + 1 && beta <= n && s <= r && (s..beta).all(|b| gcd(b, r) > 1);
        // S3
        for u in 1..r { if gcd(u, r) != 1 { continue; }
            let x = if u >= s { u } else { u + r };
            ok &= x <= n && x != r && x >= beta && (x - u) % r == 0 && gcd(x, r) == 1; }
        for m in mmin.max(2)..=mmax {
            inst += 1;
            let d = m * r + beta;
            // S2
            let mut aa = 1i128; while (aa * r + 1) % d != 0 { aa += 1; }
            let mut close: Vec<i128> = Vec::new();
            for x in 1..d { let y = (aa * x) % d; let f = y.min(d - y); if f < m { close.push(x); } }
            let mut expect: Vec<i128> = Vec::new();
            for k in 1..m { expect.push(k * r); expect.push(k * r + beta); }
            expect.sort();
            ok &= close == expect;
            let ymr = (aa * m * r) % d; ok &= ymr.min(d - ymr) == m;
            ok &= close.iter().all(|&x| x > n || x == r);
            // S4 / S5
            let (p, q) = if m * (n + 1) >= d { (m, d) } else { (1, n + 1) };
            ok &= q - r * p > 0 && m * (q - r * p) <= beta * p;
            ok &= m * (d - r * m) == beta * m; // tau0 = m/d : q-rp = d - r m = beta, m*beta == beta*m  (equality)
        }
        if !ok { bad += 1; println!("STEPFAIL N={} r={}", n, r); }
    } }
    println!("DONE vf_steps N={}..{} m={}..{} instances={} failures={}", nmin, nmax, mmin, mmax, inst, bad);
}
