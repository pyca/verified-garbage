use std::{ffi::{c_int, c_void}, hint::black_box, ptr, time::Instant};
use verified_garbage::aes_gcm::AesGcm;

#[link(name = "crypto")]
unsafe extern "C" {
    fn EVP_CIPHER_CTX_new() -> *mut c_void;
    fn EVP_CIPHER_CTX_free(ctx: *mut c_void);
    fn EVP_aes_128_gcm() -> *const c_void;
    fn EVP_aes_192_gcm() -> *const c_void;
    fn EVP_aes_256_gcm() -> *const c_void;
    fn EVP_EncryptInit_ex(ctx: *mut c_void, cipher: *const c_void, engine: *mut c_void, key: *const u8, iv: *const u8) -> c_int;
    fn EVP_EncryptUpdate(ctx: *mut c_void, out: *mut u8, out_len: *mut c_int, input: *const u8, len: c_int) -> c_int;
    fn EVP_EncryptFinal_ex(ctx: *mut c_void, out: *mut u8, out_len: *mut c_int) -> c_int;
    fn EVP_CIPHER_CTX_ctrl(ctx: *mut c_void, op: c_int, len: c_int, data: *mut c_void) -> c_int;
}

struct Ssl(*mut c_void);
impl Ssl {
    fn new(key: &[u8], nonce: &[u8]) -> Self {
        unsafe {
            let cipher = match key.len() { 16 => EVP_aes_128_gcm(), 24 => EVP_aes_192_gcm(), 32 => EVP_aes_256_gcm(), _ => unreachable!() };
            let ctx = EVP_CIPHER_CTX_new();
            assert!(!ctx.is_null());
            assert_eq!(EVP_EncryptInit_ex(ctx, cipher, ptr::null_mut(), key.as_ptr(), nonce.as_ptr()), 1);
            Self(ctx)
        }
    }
    fn seal(&mut self, nonce: &[u8], aad: &[u8], source: *const u8, n: usize, out: &mut [u8], tls: bool) -> [u8; 16] {
        let mut tag = [0; 16];
        unsafe {
            let mut len = 0;
            assert_eq!(EVP_EncryptInit_ex(self.0, ptr::null(), ptr::null_mut(), ptr::null(), nonce.as_ptr()), 1);
            assert_eq!(EVP_EncryptUpdate(self.0, ptr::null_mut(), &mut len, aad.as_ptr(), aad.len() as c_int), 1);
            assert_eq!(EVP_EncryptUpdate(self.0, out.as_mut_ptr(), &mut len, source, n as c_int), 1);
            let mut written = len as usize;
            if tls {
                assert_eq!(EVP_EncryptUpdate(self.0, out.as_mut_ptr().add(written), &mut len, [0x17].as_ptr(), 1), 1);
                written += len as usize;
            }
            assert_eq!(EVP_EncryptFinal_ex(self.0, out.as_mut_ptr().add(written), &mut len), 1);
            assert_eq!(EVP_CIPHER_CTX_ctrl(self.0, 0x10, 16, tag.as_mut_ptr().cast()), 1);
        }
        tag
    }
}
impl Drop for Ssl { fn drop(&mut self) { unsafe { EVP_CIPHER_CTX_free(self.0) } } }

fn aligned(n: usize, offset: usize) -> (Vec<u8>, usize) {
    let raw = vec![0; n + offset + 4096];
    let start = (4096 - raw.as_ptr() as usize % 4096) % 4096 + offset;
    (raw, start)
}

fn operation(v: usize, key: &AesGcm, ssl: &mut Ssl, nonce: &[u8], aad: &[u8], src: &[u8], out: &mut [u8]) -> [u8; 16] {
    let n = src.len();
    match v {
        0 => key.encrypt_in_place(black_box(nonce), black_box(aad), black_box(&mut out[..n])).unwrap(),
        1 => key.encrypt(black_box(nonce), black_box(aad), &[black_box(src)], black_box(&mut out[..n])).unwrap(),
        2 => key.encrypt(black_box(nonce), black_box(aad), &[black_box(src), black_box(&[0x17])], black_box(&mut out[..n+1])).unwrap(),
        3 => ssl.seal(black_box(nonce), black_box(aad), black_box(out.as_ptr()), n, black_box(out), false),
        4 => ssl.seal(black_box(nonce), black_box(aad), black_box(src.as_ptr()), n, black_box(out), false),
        5 => ssl.seal(black_box(nonce), black_box(aad), black_box(src.as_ptr()), n, black_box(out), true),
        _ => unreachable!(),
    }
}

fn main() {
    let nonce = [0x24; 12];
    let (mut a, ai) = aligned(5, 0);
    a[ai..ai+5].copy_from_slice(&[0x17, 3, 3, 0x40, 0x11]);
    let aad = &a[ai..ai+5];
    println!("# variant: 0 Rust/inplace, 1 Rust/outplace, 2 Rust/TLS, 3 OpenSSL/inplace, 4 OpenSSL/outplace, 5 OpenSSL/TLS");
    for bits in [128, 192, 256] {
        let raw_key = vec![0x42; bits/8];
        let key = AesGcm::new(&raw_key).unwrap();
        let mut ssl = Ssl::new(&raw_key, &nonce);
        for n in [512, 1024, 16384] {
            let (src_raw, si) = aligned(n, 5);
            let src = &src_raw[si..si+n];
            let (mut out_raw, oi) = aligned(n+17, 2053);
            let out = &mut out_raw[oi..oi+n+17];
            // Check the same ciphertext and tag before timing the public calls.
            let t1 = operation(1, &key, &mut ssl, &nonce, aad, src, out);
            let want1 = out[..n].to_vec();
            let t4 = operation(4, &key, &mut ssl, &nonce, aad, src, out);
            assert_eq!((&out[..n], t4), (&want1[..], t1));
            let t2 = operation(2, &key, &mut ssl, &nonce, aad, src, out);
            let want2 = out[..n+1].to_vec();
            let t5 = operation(5, &key, &mut ssl, &nonce, aad, src, out);
            assert_eq!((&out[..n+1], t5), (&want2[..], t2));
            let reps = if n == 16384 { 1024 } else { 4096 };
            for sample in 0..25 {
                for j in 0..6 {
                    let v = (sample+j)%6;
                    out.fill(0);
                    for _ in 0..64 { black_box(operation(v, &key, &mut ssl, &nonce, aad, src, out)); }
                    let start = Instant::now();
                    for _ in 0..reps { black_box(operation(v, &key, &mut ssl, &nonce, aad, src, out)); }
                    println!("{bits},{n},{sample},{v},{:.3}", start.elapsed().as_nanos() as f64 / reps as f64);
                }
            }
        }
    }
}
