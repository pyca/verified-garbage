module

public import VerifiedGarbage.Spec.Mgf1
public import VerifiedGarbage.Spec.Hmac

/-!
# The numbers of the hash functions

**Trusted** (as every file in `Spec/`). The number that names a hash
function to the Rust functions that take it as an argument (a public `usize`)
rather than in their name: its index in `Mgf1.hashes`, from 0 for MD5 to 13
for BLAKE2s-256, which is `RsaPkcs1Sig.Hash.ofId`'s numbering where both
name one. `mgf1` gives the hash function as RSA's padding takes it
(`Mgf1.Hash`), `hmac` as HMAC takes it (`Hmac.HashFunction`, for the
Merkle–Damgård ones, 0 to 7).
-/

@[expose] public section

namespace VG.Spec.HashId

/-- The hash function `i` names, as RSA's padding takes it: `Mgf1.hashes[i]`. -/
def mgf1 (i : Nat) : Option Mgf1.Hash := Mgf1.hashes[i]?

/-- The hash function `i` names, as HMAC takes it, for MD5 (0) to
SHA-512/256 (7). -/
def hmac : Nat → Option Hmac.HashFunction
  | 0 => some Hmac.md5 | 1 => some Hmac.sha1 | 2 => some Hmac.sha224 | 3 => some Hmac.sha256
  | 4 => some Hmac.sha384 | 5 => some Hmac.sha512 | 6 => some Hmac.sha512_224
  | 7 => some Hmac.sha512_256
  | _ => none

/-- The documentation's list of the numbers of SHA-1 and the SHA-2 functions. -/
def sha12Doc : String :=
  "1 SHA-1, 2 SHA-224, 3 SHA-256, 4 SHA-384, 5 SHA-512, 6 SHA-512/224, 7 SHA-512/256 \
    (`VG.Spec.HashId`, as `VG.Spec.RsaPkcs1Sig.Hash.ofId` numbers them)"

/-- The `# Safety` item on a buffer of `name` that must be as long as the
values of the hash function `arg` names, for SHA-1 and the SHA-2 functions. -/
def lenSafety (name arg : String) : String :=
  s!"`{name}` must be the length of `{arg}`'s values: 20 for SHA-1, 28 for SHA-224 and \
    SHA-512/224, 32 for SHA-256 and SHA-512/256, 48 for SHA-384, 64 for SHA-512."

end VG.Spec.HashId
