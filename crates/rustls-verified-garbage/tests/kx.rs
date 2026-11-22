//! Every key exchange group agrees on a secret from the two shares it makes,
//! and refuses a share that is not one.

use rustls_verified_garbage::{ALL_KX_GROUPS, kx_group};

/// A client's exchange started by each group and a server's completed with
/// the client's share give the same secret, of the group the exchanges say;
/// another exchange gives another secret.
#[test]
fn groups_agree() {
    for group in ALL_KX_GROUPS {
        let name = format!("{group:?}");
        let client = group.start().unwrap().into_single();
        assert_eq!(client.group(), group.name(), "{name}");
        let server = group.start_and_complete(client.pub_key()).unwrap();
        assert_eq!(server.group, group.name(), "{name}");
        let secret = client.complete(&server.pub_key).unwrap();
        assert_eq!(
            secret.secret_bytes(),
            server.secret.secret_bytes(),
            "{name}"
        );
        let other = group.start().unwrap().into_single();
        let other = group.start_and_complete(other.pub_key()).unwrap();
        assert_ne!(
            other.secret.secret_bytes(),
            server.secret.secret_bytes(),
            "{name}"
        );
    }
}

/// No group completes an exchange with a share one byte short, as a client
/// or as a server.
#[test]
fn truncated_shares() {
    for group in ALL_KX_GROUPS {
        let name = format!("{group:?}");
        let client = group.start().unwrap().into_single();
        let share = client.pub_key().to_vec();
        let server = group.start_and_complete(&share).unwrap();
        let short = group.start_and_complete(&share[..share.len() - 1]);
        assert!(short.is_err(), "{name}");
        let server_share = &server.pub_key[..server.pub_key.len() - 1];
        assert!(client.complete(server_share).is_err(), "{name}");
    }
}

/// A share of the right length that is no public key is refused: X25519's
/// of all zeros (a point of low order, whose shared secret is zero), a NIST
/// curve's of all zeros (no point), and an ML-KEM encapsulation key of all
/// ones (coefficients not below q).
#[test]
fn invalid_shares() {
    for group in [kx_group::X25519, kx_group::SECP256R1, kx_group::SECP384R1] {
        let client = group.start().unwrap().into_single();
        let zeros = vec![0; client.pub_key().len()];
        assert!(client.complete(&zeros).is_err(), "{group:?}");
    }
    for group in [kx_group::MLKEM768, kx_group::MLKEM1024] {
        let client = group.start().unwrap().into_single();
        let ones = vec![0xff; client.pub_key().len()];
        assert!(group.start_and_complete(&ones).is_err(), "{group:?}");
    }
}
