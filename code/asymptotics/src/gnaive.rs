// gnaive.rs: independent, unpruned, literal transcription of the Lean definitions of Gfam
// (Sext6/Gap/Defs.lean, GFam.lean): rFam N = {r in [1,N] : N < 2r}; sFam = N+1-r; betaFam = sInf{b | N+1 <= r+b /\ Coprime b r};
// mFam = beta / s + 1; PhiFam = m/(m*r+beta); Gfam = min over rFam.  Exact integer cross-multiplication (u128), all r, no pruning.
//   gnaive NLO NHI  -> lines "N num den" (G(N) reduced)
use std::env;
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }
fn main() {
    let a: Vec<String> = env::args().collect();
    let lo: u128 = a[1].parse().unwrap(); let hi: u128 = a[2].parse().unwrap();
    for n in lo..=hi {
        let mut best: Option<(u128, u128)> = None;
        for r in 1..=n { if !(n < 2 * r) { continue; }
            let s = n + 1 - r;
            let mut b = 0u128; // sInf over naturals b with N+1 <= r+b and coprime b r
            loop { if n + 1 <= r + b && gcd(b, r) == 1 { break; } b += 1; }
            let m = b / s + 1; let (nu, de) = (m, m * r + b);
            match best { None => best = Some((nu, de)), Some((bn, bd)) => { if nu * bd < bn * de { best = Some((nu, de)); } } }
        }
        let (bn, bd) = best.unwrap(); let g = gcd(bn, bd); println!("{} {} {}", n, bn / g, bd / g);
    }
}
