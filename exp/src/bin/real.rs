use std::hint::black_box;
use std::time::Instant;
use verified_garbage::aes_xts::AesXts;

fn best<F: FnMut()>(mut f: F) -> f64 {
    let mut b = f64::MAX;
    for _ in 0..30 {
        let t0 = Instant::now();
        for _ in 0..1000 { f() }
        b = b.min(t0.elapsed().as_nanos() as f64 / 1000.0);
    }
    b
}

fn main() {
    let key: [u8; 32] = core::array::from_fn(|i| i as u8);
    let i = [7u8; 16];
    for size in [64usize, 1024, 16384] {
        let data = vec![0x5au8; size];
        let mut buffer = vec![0u8; size];
        let full = best(|| {
            let ctx = AesXts::new(black_box(&key)).unwrap();
            buffer.copy_from_slice(black_box(&data));
            ctx.encrypt(black_box(&i), black_box(&mut buffer)).unwrap();
            black_box(&buffer);
        });
        let ctx = AesXts::new(&key).unwrap();
        let enc = best(|| { ctx.encrypt(black_box(&i), black_box(&mut buffer)).unwrap(); });
        let newk = best(|| { black_box(AesXts::new(black_box(&key)).unwrap()); });
        let copy = best(|| { buffer.copy_from_slice(black_box(&data)); black_box(&buffer); });
        let mut big = vec![0u8; size + 64];
        let mut offs = String::new();
        for off in [0usize, 8, 16, 32] {
            let base = big.as_ptr() as usize;
            let a = (64 - base % 64) % 64 + off;
            let t = best(|| { ctx.encrypt(black_box(&i), black_box(&mut big[a..a + size])).unwrap(); });
            offs += &format!(" off{off}={t:.0}");
        }
        println!("{size:6}: full={full:.0} encrypt={enc:.0} new={newk:.0} copy={copy:.0}{offs}");
    }
}
