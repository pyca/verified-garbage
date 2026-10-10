//! Whole RSA private-key operations (CRT, no padding): verified-garbage,
//! aws-lc and the system OpenSSL, best per-op time over many rounds.
use std::hint::black_box;
use std::time::Instant;

use openssl::rsa::{Padding, Rsa};
use verified_garbage::rsa::PrivateKey;

fn best(mut f: impl FnMut(), iters: usize) -> f64 {
    for _ in 0..iters / 4 { f() }
    let mut b = f64::MAX;
    for _ in 0..7 {
        let t = Instant::now();
        for _ in 0..iters { f() }
        b = b.min(t.elapsed().as_nanos() as f64 / iters as f64 / 1000.0);
    }
    b
}

fn main() {
    for bits in [2048u32, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let n = key.n().to_vec();
        let k = n.len();
        let vg = PrivateKey::from_crt(
            &n, &key.e().to_vec(), &key.d().to_vec(),
            &key.p().unwrap().to_vec(), &key.q().unwrap().to_vec(),
            &key.dmp1().unwrap().to_vec(), &key.dmq1().unwrap().to_vec(),
            &key.iqmp().unwrap().to_vec(),
        ).unwrap();
        let der = key.private_key_to_der().unwrap();
        let aws = unsafe { aws_lc_sys::RSA_private_key_from_bytes(der.as_ptr(), der.len()) };
        assert!(!aws.is_null());
        let mut input = vec![0x42u8; k];
        input[0] = 0;
        let mut o1 = vec![0u8; k];
        let mut o2 = vec![0u8; k];
        let mut o3 = vec![0u8; k];
        vg.private_op(&input, &mut o1).unwrap();
        let r = unsafe { aws_lc_sys::RSA_private_decrypt(k, input.as_ptr(), o2.as_mut_ptr(), aws, aws_lc_sys::RSA_NO_PADDING as i32) };
        assert_eq!(r as usize, k);
        key.private_decrypt(&input, &mut o3, Padding::NONE).unwrap();
        assert_eq!(o1, o2);
        assert_eq!(o1, o3);
        let it = match bits { 2048 => 600, 3072 => 200, _ => 100 };
        let mut res = [0f64; 3];
        for _ in 0..3 {
            let a = best(|| { black_box(&vg).private_op(black_box(&input), &mut o1).unwrap(); }, it);
            let b = best(|| unsafe { aws_lc_sys::RSA_private_decrypt(k, black_box(input.as_ptr()), o2.as_mut_ptr(), aws, aws_lc_sys::RSA_NO_PADDING as i32); }, it);
            let c = best(|| { black_box(&key).private_decrypt(black_box(&input), &mut o3, Padding::NONE).unwrap(); }, it);
            for (r, v) in res.iter_mut().zip([a, b, c]) { *r = if *r == 0.0 { v } else { r.min(v) } }
        }
        println!("{bits}: vg {:.1} us  aws-lc {:.1} us  openssl {:.1} us  vg/aws {:.3}", res[0], res[1], res[2], res[0] / res[1]);
    }
}
