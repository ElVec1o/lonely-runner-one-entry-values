// Exact integer checks for the Dusart (6.5) chain proving Lemma Q for N > 10^7.
fn pw(b: u128, e: u32) -> u128 { let mut r = 1u128; for _ in 0..e { r *= b; } r }
fn main() {
    let mut ok = true;
    let mut chk = |name: &str, c: bool| { println!("{} : {}", name, if c { "OK" } else { "FAIL" }); if !c { ok = false; } };
    // (1) ln(4/3) < 0.28769 : e^x > 4/3 for x = 28769/10^5, via Taylor partial sum to x^6 (all terms > 0, so sum <= e^x)
    // sum_{k<=6} x^k/k! with common denominator 10^30 * 720
    let den: u128 = pw(10, 30) * 720;
    let mut num: u128 = 0;
    let mut fact: u128 = 1;
    for k in 0..=6u32 {
        if k > 0 { fact *= k as u128; }
        // x^k/k! = 28769^k * 10^(5(6-k)) * (720/k!) / (10^30*720)
        num += pw(28769, k) * pw(10, 5 * (6 - k)) * (720 / fact);
    }
    chk("e^0.28769 > 4/3 (Taylor lower bound)", 3 * num > 4 * den);
    // (2) e^16 < 1.5e7 : e < 2.72, (272)^16 < 1.5*10^7 * 100^16 ; 272^8 < 3.8e19 and (3.8e19)^2 = 1.444e39 < 1.5e39
    let a = pw(272, 8);
    chk("272^8 < 3.8e19 (so 2.72^16 < 1.444e7 < 1.5e7, L>=16)", a < 38_000_000_000_000_000_000u128);
    // (3) e^17 > 1.5e7 : e > 2.7 ; 27^17 > 1.5e7 * 10^17
    chk("27^17 > 1.5e24 (so 2.7^17 > 1.5e7, L<17 at N=1e7)", pw(27, 17) > 1_500_000_000_000_000_000_000_000u128);
    // (4) Lh >= 0.5 - 1.9143/L - 2c/L^2 at L=16 with c=0.28769 : >= 37/100 ; exact rational over denominator 10^4*16*10^5*256
    // 1/2 - 19143/(10^4*16) - 57538/(10^5*256) >= 37/100
    // common denominator D = 10^5*10^4*16*256/10^? use lcm-free: multiply out with D = 10^4*16*10^5*256
    let d: u128 = pw(10, 4) * 16 * pw(10, 5) * 256;
    let lhs = d / 2 - 19143 * (d / (pw(10, 4) * 16)) - 57538 * (d / (pw(10, 5) * 256));
    chk("0.5 - 1.9143/16 - 2(0.28769)/256 >= 0.37", 100 * lhs >= 37 * d);
    // (5) N/L at N=1e7 with L<17 : 1e7/17 >= 7/0.37 (=18.92)
    chk("1e7/17 * 0.37 >= 7", 10_000_000u128 * 37 >= 7 * 17 * 100);
    // float sanity (not part of proof): Dusart bounds difference at sampled N
    for e in [7.0f64, 8.0, 10.0, 12.0, 15.0, 18.0] {
        let n = 10f64.powf(e) + 1.0;
        let lo = 2.0 * n / (2.0 * n).ln() * (1.0 + 1.0 / (2.0 * n).ln());
        let y = 1.5 * n; let up = y / y.ln() * (1.0 + 1.2762 / y.ln());
        println!("sanity N=1e{}: lower pi(2N) >= {:.4e}, upper pi(1.5N) <= {:.4e}, diff >= {:.4e}", e, lo, up, lo - up);
    }
    println!("{}", if ok { "ALL EXACT CHECKS PASSED" } else { "SOME CHECK FAILED" });
}
