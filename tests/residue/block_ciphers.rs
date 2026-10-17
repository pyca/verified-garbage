//! The block ciphers' modes: each expands its secret key's schedule into the
//! object it returns (`new`). The object, and the `Result` holding it, are
//! the caller's: they are wiped when dropped, and a move out of the
//! `Result` (`unwrap`, `?`) leaves a copy in the caller's frame.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

/// A test of each mode's `new`, with a key of the length given (`[n]` for
/// an array).
macro_rules! new {
    ($($name:ident: $ty:path, $key:tt;)*) => {
        $(
            #[test]
            fn $name() {
                super::check(stringify!($name), || {
                    let k = <$ty>::new(new!(@key $key));
                    std::hint::black_box(&k);
                });
            }
        )*
    };
    (@key [$n:literal]) => { super::secret()[..$n].try_into().unwrap() };
    (@key $n:literal) => { &super::secret()[..$n] };
}

new! {
    aes_cbc: verified_garbage::aes_cbc::AesCbc, 16;
    aes_cfb: verified_garbage::aes_cfb::AesCfb128, 16;
    aes_cfb8: verified_garbage::aes_cfb8::AesCfb8, 16;
    aes_ctr: verified_garbage::aes_ctr::AesCtr, 16;
    aes_ecb: verified_garbage::aes_ecb::AesEcb, 16;
    aes_ofb: verified_garbage::aes_ofb::AesOfb, 16;
    blowfish_cbc: verified_garbage::blowfish_cbc::BlowfishCbc, 16;
    blowfish_cfb: verified_garbage::blowfish_cfb::BlowfishCfb64, 16;
    blowfish_ofb: verified_garbage::blowfish_ofb::BlowfishOfb, 16;
    camellia_cbc: verified_garbage::camellia_cbc::CamelliaCbc, 16;
    camellia_cfb: verified_garbage::camellia_cfb::CamelliaCfb128, 16;
    camellia_ctr: verified_garbage::camellia_ctr::CamelliaCtr, 16;
    camellia_ecb: verified_garbage::camellia_ecb::CamelliaEcb, 16;
    camellia_ofb: verified_garbage::camellia_ofb::CamelliaOfb, 16;
    cast5_ecb: verified_garbage::cast5_ecb::Cast5Ecb, 16;
    idea_cfb: verified_garbage::idea_cfb::IdeaCfb64, 16;
    idea_ofb: verified_garbage::idea_ofb::IdeaOfb, 16;
    seed_cbc: verified_garbage::seed_cbc::SeedCbc, 16;
    seed_cfb: verified_garbage::seed_cfb::SeedCfb128, 16;
    seed_ecb: verified_garbage::seed_ecb::SeedEcb, [16];
    seed_ofb: verified_garbage::seed_ofb::SeedOfb, 16;
    sm4_cbc: verified_garbage::sm4_cbc::Sm4Cbc, [16];
    sm4_cfb: verified_garbage::sm4_cfb::Sm4Cfb128, [16];
    sm4_ctr: verified_garbage::sm4_ctr::Sm4Ctr, [16];
    sm4_ecb: verified_garbage::sm4_ecb::Sm4Ecb, [16];
    sm4_ofb: verified_garbage::sm4_ofb::Sm4Ofb, [16];
    triple_des_cbc: verified_garbage::triple_des_cbc::TripleDesCbc, 24;
    triple_des_cfb: verified_garbage::triple_des_cfb::TripleDesCfb64, 24;
    triple_des_cfb8: verified_garbage::triple_des_cfb8::TripleDesCfb8, 24;
    triple_des_ecb: verified_garbage::triple_des_ecb::TripleDesEcb, 24;
    triple_des_ofb: verified_garbage::triple_des_ofb::TripleDesOfb, 24;
}
