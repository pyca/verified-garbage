//! SHA-2 for the transcript hash and anywhere else rustls hashes.

use alloc::boxed::Box;

use rustls::crypto::{self, HashAlgorithm};
use verified_garbage::hashes::HashFunction;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;

pub(crate) static SHA256: Hash<Sha256> = Hash::new(HashAlgorithm::SHA256);
pub(crate) static SHA384: Hash<Sha384> = Hash::new(HashAlgorithm::SHA384);
#[allow(dead_code)] // HPKE's suites only hash with SHA-512 through HMAC.
pub(crate) static SHA512: Hash<Sha512> = Hash::new(HashAlgorithm::SHA512);

/// A hash function `H` that rustls knows as `algorithm`.
pub(crate) struct Hash<H> {
    algorithm: HashAlgorithm,
    hash: core::marker::PhantomData<fn() -> H>,
}

impl<H> Hash<H> {
    const fn new(algorithm: HashAlgorithm) -> Self {
        Self {
            algorithm,
            hash: core::marker::PhantomData,
        }
    }
}

impl<H: HashFunction + Send + Sync + 'static> crypto::hash::Hash for Hash<H> {
    fn start(&self) -> Box<dyn crypto::hash::Context> {
        Box::new(Context(H::new()))
    }

    fn hash(&self, data: &[u8]) -> crypto::hash::Output {
        crypto::hash::Output::new(H::digest(data).as_ref())
    }

    fn output_len(&self) -> usize {
        H::OUTPUT_SIZE
    }

    fn algorithm(&self) -> HashAlgorithm {
        self.algorithm
    }
}

struct Context<H>(H);

impl<H: HashFunction + Send + Sync + 'static> crypto::hash::Context for Context<H> {
    fn fork_finish(&self) -> crypto::hash::Output {
        crypto::hash::Output::new(self.0.clone().finalize().as_ref())
    }

    fn fork(&self) -> Box<dyn crypto::hash::Context> {
        Box::new(Self(self.0.clone()))
    }

    fn finish(self: Box<Self>) -> crypto::hash::Output {
        crypto::hash::Output::new(self.0.finalize().as_ref())
    }

    fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }
}
