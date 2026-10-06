//! Ed448 known-answer tests from the vendored RFC 8032, section 7.4.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::ed448::{Error, MAX_CONTEXT_LEN, SigningKey, VerifyingKey};

use super::{TEXT, hex_lines};

/// A case of section 7.4.
struct Vector {
    seed: [u8; 57],
    public: [u8; 57],
    message: Vec<u8>,
    context: Vec<u8>,
    signature: [u8; 114],
}

/// The cases of section 7.4.
fn vectors() -> Vec<Vector> {
    let section = TEXT
        .split_once("\n7.4.  Test Vectors for Ed448\n")
        .unwrap()
        .1
        .split_once("\n7.5.  Test Vectors for Ed448ph\n")
        .unwrap()
        .0;
    section
        .split("   -----")
        .filter(|case| case.contains("   SECRET KEY:"))
        .map(|case| {
            let (_, secret) = case.split_once("   SECRET KEY:").unwrap();
            let (secret, public) = secret.split_once("   PUBLIC KEY:").unwrap();
            let (public, message) = public.split_once("   MESSAGE (length ").unwrap();
            let (length, message) = message.split_once('\n').unwrap();
            let length: usize = length.split_whitespace().next().unwrap().parse().unwrap();
            let (message, signature) = message.split_once("   SIGNATURE:").unwrap();
            let (message, context) = match message.split_once("   CONTEXT:") {
                Some((message, context)) => (message, hex_lines(context)),
                None => (message, Vec::new()),
            };
            let message = hex_lines(message);
            assert_eq!(message.len(), length);
            Vector {
                seed: hex_lines(secret).try_into().unwrap(),
                public: hex_lines(public).try_into().unwrap(),
                message,
                context,
                signature: hex_lines(signature).try_into().unwrap(),
            }
        })
        .collect()
}

#[test]
fn ed448_vectors() {
    let vectors = vectors();
    assert_eq!(vectors.len(), 9);
    assert!(vectors.iter().any(|v| !v.context.is_empty()));
    for Vector {
        seed,
        public,
        message,
        context,
        signature,
    } in vectors
    {
        let key = SigningKey::from_seed(&seed);
        assert_eq!(key.seed(), &seed);
        assert_eq!(key.verifying_key().as_bytes(), &public);
        assert_eq!(key.verifying_key(), &VerifyingKey::from_bytes(&public));
        assert_eq!(key.sign_with_context(&context, &message), Ok(signature));
        assert_eq!(
            key.clone().sign_with_context(&context, &message),
            Ok(signature)
        );
        let verifying = key.verifying_key();
        assert_eq!(
            verifying.verify_with_context(&context, &message, &signature),
            Ok(())
        );
        if context.is_empty() {
            assert_eq!(key.sign(&message), signature);
            assert_eq!(verifying.verify(&message, &signature), Ok(()));
        }
        let mut changed_message = message.clone();
        changed_message.push(0);
        assert_eq!(
            verifying.verify_with_context(&context, &changed_message, &signature),
            Err(Error::InvalidSignature)
        );
        let mut changed_context = context.clone();
        changed_context.push(0);
        assert_eq!(
            verifying.verify_with_context(&changed_context, &message, &signature),
            Err(Error::InvalidSignature)
        );
        assert_eq!(
            verifying.verify_with_context(&context, &message, &signature[..113]),
            Err(Error::InvalidSignature)
        );
        assert_eq!(format!("{key:?}"), "SigningKey { .. }");
    }
}

fn rfc_key() -> SigningKey {
    SigningKey::from_seed(&vectors()[0].seed)
}

#[repr(align(8))]
struct Aligned<const N: usize>([u8; N]);

#[test]
fn context_limits() {
    let key = rfc_key();
    let context = [0x5au8; MAX_CONTEXT_LEN + 1];
    let signature = key
        .sign_with_context(&context[..MAX_CONTEXT_LEN], b"message")
        .unwrap();
    assert_eq!(
        key.verifying_key().verify_with_context(
            &context[..MAX_CONTEXT_LEN],
            b"message",
            &signature
        ),
        Ok(())
    );
    assert_eq!(
        key.sign_with_context(&context, b"message"),
        Err(Error::ContextTooLong)
    );
    // Nothing verifies with a context longer than 255 bytes.
    assert_eq!(
        key.verifying_key()
            .verify_with_context(&context, b"message", &signature),
        Err(Error::InvalidSignature)
    );
}

#[test]
fn message_boundaries_and_unaligned_inputs() {
    let key = rfc_key();
    let mut storage = Aligned([0u8; 420]);
    for (i, byte) in storage.0.iter_mut().enumerate() {
        *byte = (i as u8).wrapping_mul(29).wrapping_add(7);
    }
    // Signing hashes the ten bytes of dom4's header, the context, then a
    // 57-byte prefix or 114 bytes of R and A, then the message, with
    // SHAKE256's 136-byte blocks. Exercise messages ending at and around
    // block boundaries, with empty and nonempty contexts, starting at an
    // unaligned address.
    for context_len in [0, 1, 69, 255] {
        let context = &storage.0[3..3 + context_len];
        for len in [
            0, 1, 2, 11, 12, 13, 68, 69, 70, 135, 136, 137, 204, 205, 206, 271, 272, 273, 340,
        ] {
            let message = &storage.0[1..1 + len];
            assert_eq!(message.as_ptr() as usize % 8, 1);
            let signature = key.sign_with_context(context, message).unwrap();
            assert_eq!(key.sign_with_context(context, message), Ok(signature));
            let mut signature_storage = Aligned([0u8; 115]);
            signature_storage.0[1..].copy_from_slice(&signature);
            let signature = &signature_storage.0[1..];
            assert_eq!(signature.as_ptr() as usize % 8, 1);
            assert_eq!(
                key.verifying_key()
                    .verify_with_context(context, message, signature),
                Ok(())
            );
        }
    }
}

#[test]
fn signing_with_aliased_read_only_inputs() {
    let key = rfc_key();
    // The message and the context may alias either immutable key input to
    // cached signing. Separate copies must produce the same signature.
    let seed_copy = *key.seed();
    let public_copy = *key.verifying_key().as_bytes();
    let signature = key
        .sign_with_context(key.verifying_key().as_bytes(), key.seed())
        .unwrap();
    assert_eq!(
        key.sign_with_context(&public_copy, &seed_copy),
        Ok(signature)
    );
    assert_eq!(
        key.verifying_key()
            .verify_with_context(&public_copy, &seed_copy, &signature),
        Ok(())
    );
}
