// oe.rs : the accompanying code, author 2026-11-24. OWN engine.
// Conventions: N = number of speeds, A = N+1.  ML(V) = max_t min_{v in V} ||t v||.  V = ([N] \ {r}) u {w}.
// Method A ("gap" engine): bands B_v(tau) = {t : ||tv|| < tau} are unions of open intervals ((kq-p)/(vq),(kq+p)/(vq)), k=0..v (tau=p/q).
//   For the retained speeds R = [N]\{r} compute the exact gaps of [0,1] (closed set where all retained speeds are >= tau);
//   ge(tau): some gap contains t with ||wt|| >= tau   <=>  ML >= tau.
//   le(tau): with CLOSED bands, every open gap of the retained closed bands is inside the closed bands of w  <=>  ML <= tau.
//   ML == c  <=>  ge(c) && le(c)  (no epsilon needed).
// Method B (candidate times): ML = max over t=k/(vi+vj) of min_v ||tv||  (exact fraction).  Used only for cross-validation and exact values of exceptions.
use std::env; use std::cmp::Ordering;
type I=i128;
fn gcd(a:I,b:I)->I{ if b==0 {a.abs()} else {gcd(b,a%b)} }
#[derive(Clone,Copy)] struct F{n:I,d:I}
fn fcmp(a:F,b:F)->Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn gaps(ret:&[I], p:I, q:I, closed_bands:bool)->Vec<(F,F)>{
    let mut iv:Vec<(F,F)>=Vec::new();
    for &v in ret { for k in 0..=v { iv.push((F{n:k*q-p,d:v*q},F{n:k*q+p,d:v*q})); } }
    iv.sort_by(|a,b| fcmp(a.0,b.0));
    let mut reach=F{n:0,d:1}; let mut out=Vec::new();
    for (lo,hi) in iv {
        let gap = if closed_bands { fcmp(lo,reach)==Ordering::Greater } else { fcmp(lo,reach)!=Ordering::Less };
        if gap { out.push((reach,lo)); reach=hi; } else if fcmp(hi,reach)==Ordering::Greater { reach=hi; }
    }
    assert!(fcmp(reach,F{n:1,d:1})==Ordering::Greater, "sweep did not pass 1");
    out
}
// exists t in gap with good w-behaviour. ge-mode: closed gap [a,b], need frac(wt) in [tau,1-tau].
// le-mode: open gap (a,b), need frac(wt) in (tau,1-tau) (then ML > tau).
fn wgood(gp:&[(F,F)], w:I, p:I, q:I, ge:bool)->bool{
    for &(a,b) in gp {
        let ad=a.d; let x=(w*a.n)%ad; // frac(w a) = x/ad
        let lt_tau = x*q < p*ad;            // frac < tau
        let ge_1mt = x*q >= (q-p)*ad;       // frac >= 1-tau
        let gt_1mt = x*q > (q-p)*ad;
        if ge { if !lt_tau && !gt_1mt { return true; } } else { if !lt_tau && !ge_1mt { return true; } }
        // start = a + delta, delta = (tau - x/ad)/w  or (1 - x/ad + tau)/w
        let dnum = if lt_tau { p*ad - x*q } else { ad*q - x*q + p*ad };
        let sn = a.n*q*w + dnum; let sd = ad*q*w; // start = sn/sd
        let c = (sn*b.d).cmp(&(b.n*sd));
        if ge { if c!=Ordering::Greater { return true; } } else { if c==Ordering::Less { return true; } }
    }
    false
}
struct Eng{ g_ge:Vec<(F,F)>, g_le:Vec<(F,F)>, p:I, q:I }
fn mk(ret:&[I],p:I,q:I)->Eng{ Eng{ g_ge:gaps(ret,p,q,false), g_le:gaps(ret,p,q,true), p, q } }
impl Eng{ fn ge(&self,w:I)->bool{ wgood(&self.g_ge,w,self.p,self.q,true) }
          fn le(&self,w:I)->bool{ !wgood(&self.g_le,w,self.p,self.q,false) } }
fn ret_of(n:I,r:I)->Vec<I>{ (1..=n).filter(|&x|x!=r).collect() }
// generic set: largest element plays w
fn set_ge(v:&[I],p:I,q:I)->bool{ let mut s=v.to_vec(); s.sort(); let w=s.pop().unwrap(); mk(&s,p,q).ge(w) }
fn set_le(v:&[I],p:I,q:I)->bool{ let mut s=v.to_vec(); s.sort(); let w=s.pop().unwrap(); mk(&s,p,q).le(w) }
// Method B
fn ml_b(v:&[I])->(I,I){
    let mut best=(0i128,1i128);
    for i in 0..v.len(){ for j in i..v.len(){ let s=v[i]+v[j];
        for k in 1..=s/2 { let mut m=s; for &x in v { let y=(k*x)%s; let d=if y<s-y {y} else {s-y}; if d<m {m=d;} if m*best.1<=best.0*s {break;} }
            if m*best.1>best.0*s { best=(m,s); } } } }
    let g=gcd(best.0,best.1); (best.0/g,best.1/g)
}
fn beta(n:I,r:I)->I{ let s=n+1-r; let mut b=s; while gcd(b,r)!=1 { b+=1; } b }
// Theorem V value for 2r>N: returns (p,q) of max(1/A, m/(mr+beta))
fn val_v(n:I,r:I,m:I)->(I,I){ let a=n+1; let s=a-r; let b=beta(n,r); if m*s>=b { (m,m*r+b) } else { (1,a) } }
fn gfam(n:I)->(I,I){ let a=n+1; let mut best=(1i128,1i128);
    for r in (n/2+1)..=n { let s=a-r; let b=beta(n,r); let m=b/s+1; let (p,q)=(m,m*r+b); if p*best.1<best.0*q { best=(p,q); } } best }
fn is_prime(x:u64)->bool{ if x<2 {return false;} let mut d=2; while d*d<=x { if x%d==0 {return false;} d+=1; } true }
// witness D (Lemma R1): smallest D in [A+r,2N], gcd(D,r)=1, w mod D not in {0, r, D-r}
fn witness(n:I,r:I,w:I)->Option<I>{ let a=n+1; for d in (a+r)..=(2*n) { if gcd(d,r)!=1 {continue;} let y=w%d; if y!=0 && y!=r%d && y!=(d-r)%d { return Some(d); } } None }
fn wb(n:I,r:I)->Option<I>{ let a=n+1; let mut best:Option<I>=None;
    for d in (a+r)..=(2*n-1) { if gcd(d,r)!=1 {continue;} let num=d*n*n; let den=2*(2*n-d); let t=(num+den-1)/den; best=Some(match best{None=>t,Some(b)=>b.min(t)}); } best }
fn main(){
    let a:Vec<String>=env::args().collect();
    match a[1].as_str(){
    "ctl"=>{ // controls: planted sets, A-vs-B cross validation (fixed LCG seed)
        let mut fails=0;
        let planted:Vec<(Vec<I>,(I,I),&str)>=vec![
            (vec![1,3,4,7],(1,5),"T1 N=4 tight"),(vec![1,3,4,5,9],(1,6),"T2 N=5 tight"),
            ((1..=13).filter(|&x|x!=12).chain([36]).collect(),(3,41),"N=13 r=12 m=3 value 3/41"),
            ((1..=13).filter(|&x|x!=12).chain([24]).collect(),(1,14),"N=13 r=12 m=2 tight"),
            ((1..=13).filter(|&x|x!=6).chain([69]).collect(),(3,40),"N=13 r=6 w=69 (hb.rs: 3/40)"),
            (vec![1,2,3,4,5,6,7,8],(1,9),"[8]"),((1..=31).filter(|&x|x!=30).chain([120]).collect(),(4,127),"N=31 r=30 m=4 value 4/127"),
            ((1..=31).filter(|&x|x!=30).chain([90]).collect(),(1,32),"N=31 r=30 m=3 tight")];
        for (v,(p,q),name) in planted.iter(){
            let ok=set_ge(v,*p,*q)&&set_le(v,*p,*q); let below=!set_ge(v,*p*1000+1,*q*1000); // value + 1/(1000 q) must fail
            let bb = if v.len()<=14 && v.iter().max().unwrap()<=&140 { let b=ml_b(v); b==(*p,*q) } else { true };
            let g=gcd(*p,*q); let _=g;
            println!("ctl planted {:<34} A: ge&le at {}/{} = {} ; just above fails = {} ; B agrees = {}", name,p,q,ok,below,bb);
            if !(ok&&below&&bb) { fails+=1; } }
        // one more planted: N=5 [5]\{2} u {7}: A vs B only
        let mut seed:u64=88172645463325252; let mut nxt=||{ seed^=seed<<13; seed^=seed>>7; seed^=seed<<17; seed };
        let mut cnt=0; let mut bad=0;
        for _ in 0..4000 { let len=3+(nxt()%7) as usize; let mx=12+(nxt()%70) as I; let mut v:Vec<I>=Vec::new();
            while v.len()<len { let x=1+(nxt()%(mx as u64)) as I; if !v.contains(&x) { v.push(x); } }
            let (p,q)=ml_b(&v); let ok=set_ge(&v,p,q)&&set_le(&v,p,q);
            let up=!set_ge(&v,p*997+1,q*997) && set_le(&v,p*997+1,q*997); let dn=set_ge(&v,p*997-1,q*997) && !set_le(&v,p*997-1,q*997);
            cnt+=1; if !(ok&&up&&dn) { bad+=1; if bad<5 { println!("MISMATCH {:?} B={}/{} ok={} up={} dn={}",v,p,q,ok,up,dn); } } }
        println!("ctl random A-vs-B cross validation: {} sets, {} mismatches",cnt,bad);
        // random one-entry sets
        let mut bad2=0; let mut c2=0;
        for n in 4..=12 { for r in 1..=n { for w in (n+1)..=(3*n+9) { let mut v=ret_of(n,r); v.push(w); let (p,q)=ml_b(&v); let ok=set_ge(&v,p,q)&&set_le(&v,p,q); let up=!set_ge(&v,p*997+1,q*997); c2+=1; if !(ok&&up){bad2+=1; if bad2<5 {println!("MISMATCH1 N={} r={} w={} B={}/{}",n,r,w,p,q);} } } } }
        println!("ctl all one-entry sets N=4..12, w<=3N+9: {} sets, {} mismatches",c2,bad2);
        for n in [7i128,13,14,31,32,73,211] { let g=gfam(n); println!("G({})={}/{}",n,g.0,g.1); }
        println!("ctl summary: planted fails={} random mismatches={} one-entry mismatches={}",fails,bad,bad2);
    }
    "fin"=>{ // finite check below the analytic range: all r <= N/2, all w in (N, Wb(N,r)) ; classification: witnessed by R1, or engine ge(1/N), else exception
        let n1:I=a[2].parse().unwrap(); let n2:I=a[3].parse().unwrap();
        for n in n1..=n2 { let g=gfam(n); let (mut tot,mut wit,mut eng,mut exc,mut nod,mut lt_g)=(0u64,0u64,0u64,0u64,0u64,0u64); let mut ex=String::new(); let mut eo=String::new(); let mut wbmax:I=0; let mut wit_mismatch=0u64;
            for r in 1..=(n/2) {
                let wbv=match wb(n,r){Some(x)=>x,None=>{nod+=1; continue}}; if wbv>wbmax {wbmax=wbv;}
                let e1=mk(&ret_of(n,r),1,n); let eg=mk(&ret_of(n,r),g.0,g.1);
                for w in (n+1)..wbv { tot+=1;
                    if let Some(d)=witness(n,r,w) { wit+=1; // cross-check lemma R1 against the engine: ML >= 2/D
                        if !mk(&ret_of(n,r),2,d).ge(w) { wit_mismatch+=1; } continue; }
                    if e1.ge(w) { eng+=1; if n>=14 && eo.len()<500 { eo.push_str(&format!(" ({},{})",r,w)); } continue; }
                    exc+=1; let mut v=ret_of(n,r); v.push(w); let (p,q)=ml_b(&v); if !eg.ge(w) {lt_g+=1;}
                    if ex.len()<900 { ex.push_str(&format!(" (r={},w={},ML={}/{})",r,w,p,q)); } } }
            println!("FIN N={} sets={} witnessed={} engine_only={} EXCEPTIONS(ML<1/N)={} (below G: {}) r_without_D={} Wb_max={} R1_vs_engine_mismatch={} |{} ENGINE_ONLY_N14+:{}",n,tot,wit,eng,exc,lt_g,nod,wbmax,wit_mismatch,ex,eo);
        }
    }
    "scan"=>{ // R2/R3 re-check, w up to (1.5A)^3 : r<=N/2 -> ML>=1/N (and >=G); 2r>N: r|w -> ML == Theorem V ; r not| w -> ML >= 1/r
        let n1:I=a[2].parse().unwrap(); let n2:I=a[3].parse().unwrap();
        for n in n1..=n2 { let aa=n+1; let g=gfam(n); let wmax=(3*aa/2).pow(3);
            let (mut lo_tot,mut lo_exc,mut lo_belowg)=(0u64,0u64,0u64); let (mut hi_mult,mut hi_ok,mut hi_bad,mut hi_lt,mut hi_tight)=(0u64,0u64,0u64,0u64,0u64); let (mut nm_tot,mut nm_bad,mut nm_lt)=(0u64,0u64,0u64);
            let mut lex=String::new(); let mut hbad=String::new(); let mut minrat=(1i128,0i128); // min over hi_lt of ML/(1/N) not needed
            let _=&mut minrat;
            for r in 1..=n {
                if 2*r<=n { let e1=mk(&ret_of(n,r),1,n); let eg=mk(&ret_of(n,r),g.0,g.1);
                    for w in (n+1)..=wmax { lo_tot+=1; let okn=e1.ge(w); let okg=eg.ge(w);
                        // R1 consistency: a witness D implies ge(1/N)
                        if witness(n,r,w).is_some() && !okn { lo_exc+=1; lex.push_str(&format!(" R1BUG({},{})",r,w)); }
                        if !okn { lo_exc+=1; if lex.len()<700 { lex.push_str(&format!(" ({},{})",r,w)); } }
                        if !okg { lo_belowg+=1; } } }
                else { let e1=mk(&ret_of(n,r),1,n); let er=mk(&ret_of(n,r),1,r);
                    for w in (n+1)..=wmax {
                        if w%r==0 { let m=w/r; hi_mult+=1; let (p,q)=val_v(n,r,m); let e=mk(&ret_of(n,r),p,q);
                            let eu=mk(&ret_of(n,r),p*997+1,q*997); let ed=mk(&ret_of(n,r),p*997-1,q*997); if e.ge(w)&&e.le(w)&&!eu.ge(w)&&eu.le(w)&&ed.ge(w)&&!ed.le(w) { hi_ok+=1; } else { hi_bad+=1; if hbad.len()<300 { hbad.push_str(&format!(" ({},{})V={}/{}",r,w,p,q)); } }
                            if !e1.ge(w) { hi_lt+=1; } if (p,q)==(1,aa) { hi_tight+=1; } }
                        else { nm_tot+=1; if !er.ge(w) { nm_bad+=1; } if !e1.ge(w) { nm_lt+=1; } } } } }
            println!("SCAN N={} wmax={} | r<=N/2: sets={} ML<1/N:{} ML<G:{} [{}] | 2r>N, r|w: sets={} formula_ok={} formula_BAD={}{} ML<1/N:{} tight(=1/A):{} | 2r>N, r!|w: sets={} ML<1/r:{} ML<1/N:{}",n,wmax,lo_tot,lo_exc,lo_belowg,lex,hi_mult,hi_ok,hi_bad,hbad,hi_lt,hi_tight,nm_tot,nm_bad,nm_lt);
        }
    }
    "pr"=>{ // prime-count lemma: cnt(N,r)=#primes in [N+1+r,2N] ; need >=7 for all r<=N/2  (worst r=floor(N/2))
        let x:usize=a[2].parse().unwrap(); let top=2*x+2; let mut s=vec![true;top+1]; s[0]=false; s[1]=false; let mut i=2; while i*i<=top { if s[i] { let mut j=i*i; while j<=top { s[j]=false; j+=i; } } i+=1; }
        let mut pi=vec![0u32;top+1]; for i in 1..=top { pi[i]=pi[i-1]+if s[i]{1}else{0}; }
        let mut last_bad=0usize; let mut nbad=0usize; let mut minc_after=u32::MAX; let mut badlist=String::new();
        for n in 4..=x { let cnt=pi[2*n]-pi[n+n/2]; if cnt<7 { last_bad=n; nbad+=1; if n>=14 && badlist.len()<400 { badlist.push_str(&format!(" {}:{}",n,cnt)); } } }
        for n in (last_bad+1)..=x { let cnt=pi[2*n]-pi[n+n/2]; if cnt<minc_after {minc_after=cnt;} }
        println!("PR sieve to {} : N in 4..={} with cnt(N,floor(N/2))<7: {} ; last such N = {} ; min cnt for N in ({},{}] = {} ; bad N>=14 (N:cnt) {}",top,x,nbad,last_bad,last_bad,x,minc_after,badlist);
        // pairs (N,r) with N>=14, r<=N/2, cnt<7
        let mut pairs=0u64; let mut maxn_pair=0usize; let mut totpairs=0u64;
        for n in 14..=std::cmp::min(x,5000) { for r in 1..=n/2 { totpairs+=1; let cnt=pi[2*n]-pi[n+r]; if cnt<7 { pairs+=1; if n>maxn_pair {maxn_pair=n;} } } }
        println!("PR pairs (N,r), 14<=N<=min(x,5000), r<=N/2, with <7 primes in [N+1+r,2N]: {} of {} ; max N among them = {}",pairs,totpairs,maxn_pair);
        // RS62 sanity (numerics, evidence only): pi(p) < 1.25506 p/ln p at primes p>=2, and pi(x)>x/ln x at x=p-1 for p-1>=17
        let mut ub_fail=0; let mut lb_fail=0; for p in 2..=top { if s[p] { if (pi[p] as f64) >= 1.25506*(p as f64)/((p as f64).ln()) { ub_fail+=1; } if p-1>=17 && (pi[p-1] as f64) <= ((p-1) as f64)/(((p-1) as f64).ln()) { lb_fail+=1; } } }
        println!("PR RS62 sanity (float, evidence only) up to {}: upper-bound failures {} lower-bound failures {}",top,ub_fail,lb_fail);
        // analytic bound at N=1e7 and beyond (RS62): bracket*(N/L)
        for &nn in &[2000f64,5000.0,10000.0,1e7,1e9,1e12] { let l=(1.5*nn+1.0).ln(); let br=2.0*l/(l+(4.0f64/3.0).ln())-1.25506*(1.5+1.0/nn); println!("PR analytic lower bound on #primes in (1.5N+1,2N] at N={:e}: {:.1}",nn,nn/l*br); }
        let _=is_prime(2);
    }
    "lt"=>{ // test Lemma L: for w in [Wb, Wb+span) the engine must give ML >= 1/N (r<=N/2, N in n1..n2)
        let n1:I=a[2].parse().unwrap(); let n2:I=a[3].parse().unwrap(); let span:I=a[4].parse().unwrap();
        for n in n1..=n2 { let (mut tot,mut bad)=(0u64,0u64); let mut ex=String::new();
            for r in 1..=(n/2) { let wbv=match wb(n,r){Some(x)=>x,None=>continue}; let e1=mk(&ret_of(n,r),1,n);
                for w in wbv..(wbv+span) { tot+=1; if !e1.ge(w) { bad+=1; if ex.len()<300 { ex.push_str(&format!(" ({},{})",r,w)); } } } }
            println!("LT N={} sets={} ML<1/N:{} |{}",n,tot,bad,ex); }
    }
    "stress"=>{ // structured + random large w: CRT-built w that is bad (w = e r mod P) for k primes of the window, k=3..5, plus uniform random w up to 1e12; engine must give ML >= 1/N (N in n1..n2, r<=N/2)
        let n1:I=a[2].parse().unwrap(); let n2:I=a[3].parse().unwrap(); let samples:u64=a[4].parse().unwrap();
        let mut seed:u64=0x9E3779B97F4A7C15; let mut nxt=||{ seed^=seed<<13; seed^=seed>>7; seed^=seed<<17; seed };
        let egcd=|a:I,b:I|->(I,I,I){ let (mut r0,mut r1,mut s0,mut s1,mut t0,mut t1)=(a,b,1i128,0i128,0i128,1i128); while r1!=0 { let q=r0/r1; let t=r0-q*r1; r0=r1; r1=t; let t=s0-q*s1; s0=s1; s1=t; let t=t0-q*t1; t0=t1; t1=t; } (r0,s0,t0) };
        let (mut tot_c,mut bad_c,mut tot_u,mut bad_u)=(0u64,0u64,0u64,0u64); let mut ex=String::new();
        for _ in 0..samples { let n=n1+(nxt()%((n2-n1+1) as u64)) as I; let r=1+(nxt()%((n/2) as u64)) as I; let a0=n+1+r;
            let primes:Vec<I>=(a0..=(2*n)).filter(|&d| is_prime(d as u64)).collect(); if primes.len()<3 { continue; }
            let e1=mk(&ret_of(n,r),1,n);
            let k=3+(nxt()%3) as usize; let k=k.min(primes.len()); let mut chosen:Vec<I>=Vec::new(); while chosen.len()<k { let p=primes[(nxt()%(primes.len() as u64)) as usize]; if !chosen.contains(&p) { chosen.push(p); } }
            let (mut x,mut m)=(0i128,1i128);
            for &p in &chosen { let e=(nxt()%3) as i128-1; let ap=((e*r)%p+p)%p; let (_,s,_)=egcd(m,p); let invm=((s%p)+p)%p; let t=(((ap-x)%p+p)%p*invm)%p; x=x+m*t; m*=p; }
            for j in 0..3i128 { let w=x+j*m; if w<=n {continue;} tot_c+=1; if !e1.ge(w) { bad_c+=1; if ex.len()<300 { ex.push_str(&format!(" C(N={},r={},w={})",n,r,w)); } } }
            let w=(n+1)+(nxt()%1_000_000_000_000u64) as I; tot_u+=1; if !e1.ge(w) { bad_u+=1; if ex.len()<300 { ex.push_str(&format!(" U(N={},r={},w={})",n,r,w)); } }
        }
        println!("STRESS N in {}..{} samples={} | CRT-structured w (bad for 3..5 window primes): {} sets, ML<1/N: {} | uniform w<=1e12: {} sets, ML<1/N: {} |{}",n1,n2,samples,tot_c,bad_c,tot_u,bad_u,ex);
    }
    "wb"=>{ let n1:I=a[2].parse().unwrap(); let n2:I=a[3].parse().unwrap(); for n in n1..=n2 { let mut mx=0; let mut none=0; for r in 1..=n/2 { match wb(n,r){Some(x)=>{if x>mx {mx=x;}},None=>{none+=1;}} } println!("WB N={} max_r Wb={} r_without_D={}",n,mx,none); } }
    _=>{}
    }
}
