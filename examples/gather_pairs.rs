use std::{hint::black_box,time::Instant};
use verified_garbage::aead::aes_gcm::AesGcm;

#[repr(align(64))]
struct Buffer([u8;32768]);
#[inline(never)]
fn sample<const CACHED:bool>(k:&AesGcm,nonce:&[u8],aad:&[u8],pieces:&[&[u8]],dst:&mut[u8],count:usize)->f64{
    let t=Instant::now();
    for _ in 0..count {
        let tag=if CACHED{k.bench_cached_encrypt(black_box(nonce),black_box(aad),black_box(pieces),black_box(&mut *dst))}
          else {k.encrypt(black_box(nonce),black_box(aad),black_box(pieces),black_box(&mut *dst))}.unwrap();black_box(tag);
    }
    t.elapsed().as_nanos() as f64/count as f64
}
fn main(){
    let quick=std::env::var_os("CHECK_ONLY").is_some();
    let aad=[23,3,3,0,32];let nonce=[19u8;12];let mut input=Box::new(Buffer([0;32768]));
    for (i,x) in input.0.iter_mut().enumerate(){*x=(i*29+11) as u8;}
    let mut dst=Box::new(Buffer([0;32768]));
    let sizes=[1usize,16,17,64,96,97,128,224,225,511,768,769,1024,1536,4096,8192,16384];
    let mut cases=vec![];
    for bits in [128usize,192,256] {for &n in &sizes {for mode in 0..4 {
        if n<511 && mode>=2 {continue} if n==1&&mode==0 {continue}
        cases.push((bits,n,mode));
    }}}
    let mut seed=12387456u64;
    for i in (1..cases.len()).rev(){seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);let j=(seed>>32) as usize%(i+1);cases.swap(i,j)}
    for (bits,n,mode) in cases {
        let key=AesGcm::new(&[71u8;32][..bits/8]).unwrap();let p=&input.0[0..n];let mut parts=[&p[..];4];
        let count=match mode{
            0=>{parts[0]=&p[..n-1];parts[1]=&p[n-1..];2},
            1=>1,
            2|3=>{let middle=(n/2)&!15;let mid=middle+if mode==3{7}else{0};parts[0]=&p[..mid];parts[1]=&p[mid..];2}
            _=>unreachable!()};
        let pieces=&parts[..count];let mut expected=p.to_vec();let want=key.encrypt_in_place(&nonce,&aad,&mut expected).unwrap();
        for cached in [false,true] {
            let out=&mut dst.0[13..13+n];out.fill(0x39);
            let tag=if cached {key.bench_cached_encrypt(&nonce,&aad,pieces,out)} else {key.encrypt(&nonce,&aad,pieces,out)}.unwrap();
            assert_eq!(out,expected);assert_eq!(tag,want);
        }
        if quick{continue}
        let out=&mut dst.0[13..13+n];let ns=sample::<false>(&key,&nonce,&aad,pieces,out,64).max(10.);
        let reps=(300_000./ns).ceil() as usize;
        for i in 0..16 {let order=(i+mode)%2==0;
            let a=if order{sample::<false>(&key,&nonce,&aad,pieces,out,reps)}else{sample::<true>(&key,&nonce,&aad,pieces,out,reps)};
            let b=if order{sample::<true>(&key,&nonce,&aad,pieces,out,reps)}else{sample::<false>(&key,&nonce,&aad,pieces,out,reps)};
            println!("{bits},{n},{mode},{i},{:.4},{:.4}",if order{a}else{b},if order{b}else{a});
        }
    }
}
