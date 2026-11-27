//! The provider's `CryptoProvider` values: what each offers, and that its
//! random number generator and ticketer work.

use rustls_verified_garbage::{
    DEFAULT_PROVIDER, DEFAULT_TLS12_PROVIDER, DEFAULT_TLS13_PROVIDER, cipher_suite, kx_group,
};

/// The default provider offers every suite and, of the groups, those it
/// says, in order; its TLS 1.2 and TLS 1.3 variants each offer only their own version's suites.
#[test]
fn providers() {
    let p = &DEFAULT_PROVIDER;
    assert_eq!(
        p.tls12_cipher_suites[..],
        cipher_suite::ALL_TLS12_CIPHER_SUITES[..]
    );
    assert_eq!(
        p.tls13_cipher_suites[..],
        cipher_suite::ALL_TLS13_CIPHER_SUITES[..]
    );
    let names = |groups: &[&dyn rustls::crypto::kx::SupportedKxGroup]| {
        groups.iter().map(|g| g.name()).collect::<Vec<_>>()
    };
    let groups = [
        kx_group::X25519MLKEM768,
        kx_group::X25519,
        kx_group::SECP256R1,
        kx_group::SECP384R1,
    ];
    assert_eq!(names(&p.kx_groups), names(&groups));
    assert!(DEFAULT_TLS13_PROVIDER.tls12_cipher_suites.is_empty());
    assert_eq!(
        DEFAULT_TLS13_PROVIDER.tls13_cipher_suites[..],
        p.tls13_cipher_suites[..]
    );
    assert!(DEFAULT_TLS12_PROVIDER.tls13_cipher_suites.is_empty());
    assert_eq!(
        DEFAULT_TLS12_PROVIDER.tls12_cipher_suites[..],
        p.tls12_cipher_suites[..]
    );
}

/// The random number generator fills a buffer, differently each time.
#[test]
fn secure_random() {
    let (mut a, mut b) = ([0u8; 32], [0u8; 32]);
    DEFAULT_PROVIDER.secure_random.fill(&mut a).unwrap();
    DEFAULT_PROVIDER.secure_random.fill(&mut b).unwrap();
    assert_ne!(a, b);
}

/// The ticketer opens the tickets it made, but not another ticketer's.
#[test]
fn ticketer() {
    let ticketer = DEFAULT_PROVIDER.ticketer_factory.ticketer().unwrap();
    let ticket = ticketer.encrypt(b"session").unwrap();
    assert_eq!(ticketer.decrypt(&ticket).unwrap(), b"session");
    let other = DEFAULT_PROVIDER.ticketer_factory.ticketer().unwrap();
    assert!(other.decrypt(&ticket).is_none());
}
