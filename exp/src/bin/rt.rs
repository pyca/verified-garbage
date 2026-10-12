use std::hint::black_box;
use std::time::Instant;
use verified_garbage::aes_gcm_siv::AesGcmSiv;

fn main() {
    // Round trips: the verified seal, then open, for many lengths and both key sizes;
    // a corrupted tag must fail and zero the data.
    let mut n = 0;
    for klen in [16usize, 32] {
        let key: Vec<u8> = (0..klen).map(|i| (i * 13 + 1) as u8).collect();
        let ctx = AesGcmSiv::new(&key).unwrap();
        for len in (0..1200).chain([4095, 4096, 4097, 8191, 16383, 16384, 16385, 20000]) {
            for alen in [0usize, 1, 17, 300] {
                let nonce = [len as u8; 12];
                let aad: Vec<u8> = (0..alen).map(|i| (i * 7 + len) as u8).collect();
                let pt: Vec<u8> = (0..len).map(|i| (i * 31 + 5) as u8).collect();
                let mut d = pt.clone();
                let tag = ctx.encrypt_in_place(&nonce, &aad, &mut d).unwrap();
                let mut e = d.clone();
                ctx.decrypt_in_place(&nonce, &aad, &mut e, &tag).expect("open failed");
                assert_eq!(e, pt, "len {len} alen {alen}");
                let mut bad = tag; bad[3] ^= 1;
                let mut f = d.clone();
                assert!(ctx.decrypt_in_place(&nonce, &aad, &mut f, &bad).is_err());
                assert!(f.iter().all(|&b| b == 0));
                n += 1;
            }
        }
    }
    println!("round trips ok: {n}");
    let key = [7u8; 16];
    for size in [64usize, 1024, 16384] {
        let data = vec![0x5au8; size];
        let ctx = AesGcmSiv::new(&key).unwrap();
        let nonce = [1u8; 12];
        let mut ct = data.clone();
        let tag = ctx.encrypt_in_place(&nonce, &[], &mut ct).unwrap();
        let mut best = f64::MAX;
        let mut buf = ct.clone();
        for _ in 0..30 {
            let t0 = Instant::now();
            for _ in 0..1000 {
                buf.copy_from_slice(&ct);
                let c = AesGcmSiv::new(black_box(&key)).unwrap();
                c.decrypt_in_place(black_box(&nonce), &[], black_box(&mut buf), &tag).unwrap();
            }
            best = best.min(t0.elapsed().as_nanos() as f64 / 1000.0);
        }
        println!("open {size}: {best:.0} ns");
    }
}
