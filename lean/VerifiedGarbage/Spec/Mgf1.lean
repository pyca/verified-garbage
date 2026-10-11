module

public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Spec.Blake2

/-!
# MGF1 (RFC 8017 Appendix B.2.1), and the hash functions RSA's padding uses

**Trusted** (as every file in `Spec/`). The mask generation function MGF1 of
PKCS #1 v2.2 (RFC 8017), Appendix B.2.1, over any hash function, and the hash
functions the library implements, which RSASSA-PSS (`Spec/RsaPss.lean`) and
RSAES-OAEP take both as their hash function and as MGF1's, each with its
digest length `hLen`. Appendix B.1 allows any hash function and lists those
of the MD5, SHA-1 and SHA-2 families; the others are the library's other hash
functions of a fixed digest length: SHA-3 (FIPS 202), and BLAKE2 (RFC 7693),
unkeyed, with its longest digests.
-/

@[expose] public section

namespace VG.Spec.Mgf1

/-- A hash function as RSA's padding uses it: its name, the name that stands
for it in Rust names (`sha256`), the Lean name of this record (for the
documentation), its digest length `hLen` in octets, and the digest of a
message. -/
structure Hash where
  name : String
  rust : String
  lean : String
  len : Nat
  hash : List Byte → List Byte

/-- MD5 (RFC 1321): 16-octet digests. -/
def md5 : Hash := ⟨"MD5", "md5", "md5", 16, Md5.hash⟩

/-- SHA-1 (FIPS 180-4): 20-octet digests. -/
def sha1 : Hash := ⟨"SHA-1", "sha1", "sha1", 20, Sha1.hash⟩

/-- SHA-224 (FIPS 180-4): 28-octet digests. -/
def sha224 : Hash := ⟨"SHA-224", "sha224", "sha224", 28, Sha256.sha224⟩

/-- SHA-256 (FIPS 180-4): 32-octet digests. -/
def sha256 : Hash := ⟨"SHA-256", "sha256", "sha256", 32, Sha256.hash⟩

/-- SHA-384 (FIPS 180-4): 48-octet digests. -/
def sha384 : Hash := ⟨"SHA-384", "sha384", "sha384", 48, Sha512.sha384⟩

/-- SHA-512 (FIPS 180-4): 64-octet digests. -/
def sha512 : Hash := ⟨"SHA-512", "sha512", "sha512", 64, Sha512.sha512⟩

/-- SHA-512/224 (FIPS 180-4): 28-octet digests. -/
def sha512_224 : Hash := ⟨"SHA-512/224", "sha512_224", "sha512_224", 28, Sha512.sha512_224⟩

/-- SHA-512/256 (FIPS 180-4): 32-octet digests. -/
def sha512_256 : Hash := ⟨"SHA-512/256", "sha512_256", "sha512_256", 32, Sha512.sha512_256⟩

/-- SHA3-224 (FIPS 202): 28-octet digests. -/
def sha3_224 : Hash := ⟨"SHA3-224", "sha3_224", "sha3_224", 28, Sha3.sha3_224⟩

/-- SHA3-256 (FIPS 202): 32-octet digests. -/
def sha3_256 : Hash := ⟨"SHA3-256", "sha3_256", "sha3_256", 32, Sha3.sha3_256⟩

/-- SHA3-384 (FIPS 202): 48-octet digests. -/
def sha3_384 : Hash := ⟨"SHA3-384", "sha3_384", "sha3_384", 48, Sha3.sha3_384⟩

/-- SHA3-512 (FIPS 202): 64-octet digests. -/
def sha3_512 : Hash := ⟨"SHA3-512", "sha3_512", "sha3_512", 64, Sha3.sha3_512⟩

/-- BLAKE2b-512 (RFC 7693): unkeyed BLAKE2b with 64-octet digests. -/
def blake2b512 : Hash := ⟨"BLAKE2b-512", "blake2b512", "blake2b512", 64, Blake2.blake2b 64 []⟩

/-- BLAKE2s-256 (RFC 7693): unkeyed BLAKE2s with 32-octet digests. -/
def blake2s256 : Hash := ⟨"BLAKE2s-256", "blake2s256", "blake2s256", 32, Blake2.blake2s 32 []⟩

/-- Every hash function above. -/
def hashes : List Hash :=
  [md5, sha1, sha224, sha256, sha384, sha512, sha512_224, sha512_256, sha3_224, sha3_256,
    sha3_384, sha3_512, blake2b512, blake2s256]

/-- The octetwise exclusive-or of two octet strings (of the length of the
shorter). -/
def xorBytes (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b

/-- `MGF1(mgfSeed, maskLen)` (Appendix B.2.1) with the hash function `H`:
the leading `maskLen` octets of `T = Hash(mgfSeed ‖ C)` concatenated for
`counter` from 0 to `⌈maskLen / hLen⌉ - 1`, where `C = I2OSP(counter, 4)`
(steps 2–4).

Step 1's error, for `maskLen > 2^32 hLen`, is left out: every mask here is
shorter than the modulus, of at most 1024 octets. -/
def mgf1 (H : Hash) (seed : List Byte) (maskLen : Nat) : List Byte :=
  ((List.range ((maskLen + H.len - 1) / H.len)).flatMap fun counter =>
    H.hash (seed ++ Rsa.i2osp counter 4)).take maskLen

end VG.Spec.Mgf1
