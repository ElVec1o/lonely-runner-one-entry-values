// float sanity (evidence only): Dusart (6.5) at every integer n <= 2e7
fn main(){
    let lim=20_000_000usize; let mut is=vec![true;lim+1]; is[0]=false; is[1]=false;
    let mut i=2; while i*i<=lim { if is[i]{ let mut j=i*i; while j<=lim {is[j]=false;j+=i;} } i+=1; }
    let (mut pi,mut bl,mut bu)=(0u64,0u64,0u64); let mut minlow=f64::MAX; let mut minup=f64::MAX;
    for n in 2..=lim { if is[n]{pi+=1;} let x=n as f64; let l=x.ln();
        let up=x/l*(1.0+1.2762/l); let su=up-(pi as f64); if su<minup {minup=su;} if su< -1e-9 {bu+=1;}
        if n>=599 { let lo=x/l*(1.0+1.0/l); let sl=(pi as f64)-lo; if sl<minlow {minlow=sl;} if sl< -1e-9 {bl+=1;} } }
    println!("upper violations {} (min slack {:.4}); lower violations {} (min slack {:.4})",bu,minup,bl,minlow);
}
