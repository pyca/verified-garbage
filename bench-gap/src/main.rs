mod mb;
// Scratch: sign N times with one library; for timing and SDE counts.
use aws_lc_rs::digest::{Digest, SHA256};
use aws_lc_rs::rsa::KeyPairComponents;
use aws_lc_rs::signature::{RSA_PKCS1_SHA256, RsaKeyPair, RsaPublicKeyComponents};
use openssl::rsa::Rsa;
use verified_garbage::rsa::PrivateKey;
use verified_garbage::rsa_pkcs1_sig::{Hash, sign};
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a[1] == "mb" { for b in [1024, 1536, 2048] { mb::run(b); } return; }
    let (lib, n, bits): (&str, usize, u32) = (&a[1], a[2].parse().unwrap(), a.get(3).map_or(2048, |s| s.parse().unwrap()));
    let path = format!("{}/key{bits}.pem", env!("CARGO_MANIFEST_DIR"));
    let key = match std::fs::read(&path) {
        Ok(p) => Rsa::private_key_from_pem(&p).unwrap(),
        Err(_) => { let k = Rsa::generate(bits).unwrap(); std::fs::write(&path, k.private_key_to_pem().unwrap()).unwrap(); k }
    };
    let digest = [0x42u8; 32];
    let v = |b: &openssl::bn::BigNumRef| b.to_vec();
    if lib == "crt" {
        use core::arch::x86_64::_rdtsc;
        use aws_lc_sys as s;
        let k = PrivateKey::from_crt(&v(key.n()), &v(key.e()), &v(key.d()), &v(key.p().unwrap()), &v(key.q().unwrap()), &v(key.dmp1().unwrap()), &v(key.dmq1().unwrap()), &v(key.iqmp().unwrap())).unwrap();
        let mut input = vec![0x42u8; key.n().num_bytes() as usize]; input[0] = 0;
        let c = k.mb_crt(&input, n);
        println!("bare crt {} checked {}", c[1], c[0]);
        if std::env::var("ONLY_CRT").is_ok() { return; }
        let mut vs = u64::MAX; for _ in 0..n { let t = unsafe { _rdtsc() }; std::hint::black_box(sign(&k, &digest, Hash::Sha256).unwrap()); vs = vs.min(unsafe { _rdtsc() } - t); }
        let (nn, e) = (v(key.n()), v(key.e()));
        let ak = RsaKeyPair::from_components(&KeyPairComponents {
            public_key: RsaPublicKeyComponents { n: &nn, e: &e }, d: v(key.d()), p: v(key.p().unwrap()), q: v(key.q().unwrap()),
            dP: v(key.dmp1().unwrap()), dQ: v(key.dmq1().unwrap()), qInv: v(key.iqmp().unwrap()) }).unwrap();
        let mut out = vec![0; nn.len()];
        let mut asg = u64::MAX; for _ in 0..n { let t = unsafe { _rdtsc() }; let d = Digest::import_less_safe(&digest, &SHA256).unwrap(); ak.sign_digest(&RSA_PKCS1_SHA256, &d, &mut out).unwrap(); asg = asg.min(unsafe { _rdtsc() } - t); }
        let mexp = |m: &[u8], ex: &[u8]| unsafe {
            let bn = |x: &[u8]| s::BN_bin2bn(x.as_ptr(), x.len(), core::ptr::null_mut());
            let (mm, x, ee, r) = (bn(m), bn(&input[..m.len() - 1]), bn(ex), s::BN_new());
            let ctx = s::BN_CTX_new();
            let mont = s::BN_MONT_CTX_new_for_modulus(mm, ctx);
            let mut b = u64::MAX;
            for _ in 0..n { let t = _rdtsc(); assert_eq!(s::BN_mod_exp_mont_consttime(r, x, ee, mm, ctx, mont), 1); b = b.min(_rdtsc() - t); }
            b
        };
        let (ap, aq) = (mexp(&v(key.p().unwrap()), &v(key.dmp1().unwrap())), mexp(&v(key.q().unwrap()), &v(key.dmq1().unwrap())));
        println!("{bits} best TSC ticks: vg sign {vs}, private_checked {}, bare crt {} | aws sign {asg}, modexp p {ap} + q {aq} = {}", c[0], c[1], ap + aq);
        return;
    }
    if lib == "ab" {
        let k = PrivateKey::from_crt(&v(key.n()), &v(key.e()), &v(key.d()), &v(key.p().unwrap()), &v(key.q().unwrap()), &v(key.dmp1().unwrap()), &v(key.dmq1().unwrap()), &v(key.iqmp().unwrap())).unwrap();
        let (nn, e) = (v(key.n()), v(key.e()));
        let ak = RsaKeyPair::from_components(&KeyPairComponents {
            public_key: RsaPublicKeyComponents { n: &nn, e: &e }, d: v(key.d()), p: v(key.p().unwrap()), q: v(key.q().unwrap()),
            dP: v(key.dmp1().unwrap()), dQ: v(key.dmq1().unwrap()), qInv: v(key.iqmp().unwrap()) }).unwrap();
        let mut out = vec![0; nn.len()];
        let (mut tv, mut ta, mut r) = (vec![], vec![], vec![]);
        for _ in 0..n {
            let t = std::time::Instant::now(); std::hint::black_box(sign(&k, &digest, Hash::Sha256).unwrap()); let x = t.elapsed().as_nanos() as f64;
            let t = std::time::Instant::now(); let d = Digest::import_less_safe(&digest, &SHA256).unwrap(); ak.sign_digest(&RSA_PKCS1_SHA256, &d, &mut out).unwrap(); let y = t.elapsed().as_nanos() as f64;
            tv.push(x); ta.push(y); r.push(x / y);
        }
        for q in [&mut tv, &mut ta, &mut r] { q.sort_by(|a, b| a.partial_cmp(b).unwrap()); }
        let m = n / 2;
        println!("{bits}: vg {:.1} us, aws {:.1} us (medians); vg/aws median {:.3}; mins {:.1} / {:.1}", tv[m] / 1e3, ta[m] / 1e3, r[m], tv[0] / 1e3, ta[0] / 1e3);
        return;
    }
    let t = std::time::Instant::now();
    if lib == "vg" {
        let k = PrivateKey::from_crt(&v(key.n()), &v(key.e()), &v(key.d()), &v(key.p().unwrap()), &v(key.q().unwrap()), &v(key.dmp1().unwrap()), &v(key.dmq1().unwrap()), &v(key.iqmp().unwrap())).unwrap();
        let t0 = std::time::Instant::now();
        for _ in 0..n { std::hint::black_box(sign(&k, &digest, Hash::Sha256).unwrap()); }
        eprintln!("vg: setup {:?}, {:.1} us/sign", t0 - t, t0.elapsed().as_secs_f64() * 1e6 / n as f64);
    } else {
        let (nn, e) = (v(key.n()), v(key.e()));
        let k = RsaKeyPair::from_components(&KeyPairComponents {
            public_key: RsaPublicKeyComponents { n: &nn, e: &e }, d: v(key.d()), p: v(key.p().unwrap()), q: v(key.q().unwrap()),
            dP: v(key.dmp1().unwrap()), dQ: v(key.dmq1().unwrap()), qInv: v(key.iqmp().unwrap()) }).unwrap();
        let mut out = vec![0; nn.len()];
        let t0 = std::time::Instant::now();
        for _ in 0..n { let d = Digest::import_less_safe(&digest, &SHA256).unwrap(); k.sign_digest(&RSA_PKCS1_SHA256, &d, &mut out).unwrap(); std::hint::black_box(&out); }
        eprintln!("aws: setup {:?}, {:.1} us/sign", t0 - t, t0.elapsed().as_secs_f64() * 1e6 / n as f64);
    }
}
