import VerifiedGarbage.Spec.Rsa

/-!
# RSASSA-PKCS1-v1_5 (RFC 8017 §8.2, EMSA-PKCS1-v1_5 §9.2)

**Trusted** (as every file in `Spec/`). PKCS #1 v1.5 signatures over the
RSA primitives of `Spec/Rsa.lean`, with the message already hashed: the
hash function `Hash` is named, and its value `H` is the input, as in
BoringSSL's `RSA_sign` and `RSA_verify` (step 1 of EMSA-PKCS1-v1_5-ENCODE,
`H = Hash(M)`, is the caller's).

* `encode`: EMSA-PKCS1-v1_5-ENCODE (§9.2) steps 2–6,
  `EM = 0x00 ‖ 0x01 ‖ PS ‖ 0x00 ‖ T`, with `T` the DER encoding of the
  `DigestInfo` of `H` (`digestInfo`), from note 1's table of prefixes.
* `verify`: RSASSA-PKCS1-V1_5-VERIFY (§8.2.2) as BoringSSL's
  `rsa_verify_no_self_test` computes it: RSAVP1, then the padding check of
  `RSA_padding_check_PKCS1_type_1` (`unpad`), then an exact comparison of
  what follows the padding with the `DigestInfo` it builds for the given
  hash and value. The received `DigestInfo` is never parsed. `verifyRfc` is
  §8.2.2 as written (encode, then compare), and `Proof/RsaPkcs1Sig/Verify.lean`
  proves the two equal and that `verify` accepts exactly when `s^e mod n` is
  the encoding of the given value.
* `recover`: what BoringSSL's `EVP_PKEY_verify_recover` returns for an RSA
  key with PKCS #1 v1.5 padding and a hash set (`pkey_rsa_verify_recover`,
  `crypto/evp/p_rsa.cc`): RSAVP1 and the same padding check, then the
  `DigestInfo` must be exactly as long as the hash's, with all but the last
  `hLen` octets equal to the hash's prefix; the last `hLen` octets are the
  result. OpenSSL's `ossl_rsa_verify` with `rm` (`crypto/rsa/rsa_sign.c`)
  takes the same last octets and requires the whole to equal the encoding it
  builds of them, which is the same condition. So `recover` returns `H`
  exactly when `verify` accepts `H` (`Proof/RsaPkcs1Sig/Verify.lean`): the
  digest is never parsed out of a `DigestInfo` either.

* `sign`: RSASSA-PKCS1-V1_5-SIGN (§8.2.1): `encode`, then RSASP1 checked
  against the public exponent (`Rsa.privateChecked`), which releases the
  signature only if `s^e mod n` is the encoding, as BoringSSL's
  `rsa_sign_no_self_test` (through `rsa_default_private_transform`) does.
  `Proof/RsaPkcs1Sig/Sign.lean` proves that `verify` accepts every
  signature `sign` releases, and that `sign` releases one for every value
  of the hash and every key `Rsa.checkKey` accepts whose `p` and `q` are
  prime.

The public key's checks are BoringSSL's (`Rsa.publicOpChecked`: the modulus,
and `e` odd and from 3 to 33 bits), which `rsa_verify_raw_no_self_test` runs
before RSAVP1.

`Hash.ofId` numbers the hash functions for the Rust functions (a public
`u32`). The prefixes are RFC 8017 §9.2 note 1's for the eight hash
functions of Appendix B.1 that the library implements (MD2 is not), and
for SHA3-224, SHA3-256, SHA3-384 and SHA3-512, which RFC 8017 predates, the
`DigestInfo` of their NIST object identifiers `id-sha3-224` … `id-sha3-512`
(2.16.840.1.101.3.4.2.7 to .10, NIST's Computer Security Objects Register)
with NULL parameters, as OpenSSL's `crypto/rsa/rsa_sign.c` encodes them
(`ENCODE_DIGESTINFO_SHA(sha3_224, 0x07, …)` …); BoringSSL has no SHA-3
prefixes. `Proof/RsaPkcs1Sig/Prefix.lean` checks that every prefix is the
DER encoding of a `DigestInfo` with the hash's object identifier, NULL
parameters and an `hLen`-octet digest.
-/

namespace VG.Spec.RsaPkcs1Sig

open Rsa

/-- The hash functions whose values PKCS #1 v1.5 signatures here sign. -/
inductive Hash
  | md5 | sha1 | sha224 | sha256 | sha384 | sha512 | sha512_224 | sha512_256
  | sha3_224 | sha3_256 | sha3_384 | sha3_512
  deriving DecidableEq, Repr

/-- The hash function a Rust function's `hash` argument names: 0 to 11, in
the order of `Hash`'s constructors; `none` for any other value. -/
def Hash.ofId : Nat → Option Hash
  | 0 => some .md5 | 1 => some .sha1 | 2 => some .sha224 | 3 => some .sha256
  | 4 => some .sha384 | 5 => some .sha512 | 6 => some .sha512_224 | 7 => some .sha512_256
  | 8 => some .sha3_224 | 9 => some .sha3_256 | 10 => some .sha3_384 | 11 => some .sha3_512
  | _ => none

/-- `hLen`, the length in octets of the hash's value. -/
def Hash.len : Hash → Nat
  | .md5 => 16 | .sha1 => 20 | .sha224 => 28 | .sha256 => 32 | .sha384 => 48
  | .sha512 => 64 | .sha512_224 => 28 | .sha512_256 => 32
  | .sha3_224 => 28 | .sha3_256 => 32 | .sha3_384 => 48 | .sha3_512 => 64

/-- The DER encoding of the hash's `DigestInfo` but for the value `H`
(§9.2 note 1: `T = prefix ‖ H`). -/
def Hash.prefix : Hash → List Byte
  | .md5 => [0x30, 0x20, 0x30, 0x0c, 0x06, 0x08, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x02, 0x05,
      0x05, 0x00, 0x04, 0x10]
  | .sha1 => [0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 0x03, 0x02, 0x1a, 0x05, 0x00, 0x04,
      0x14]
  | .sha224 => [0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04,
      0x02, 0x04, 0x05, 0x00, 0x04, 0x1c]
  | .sha256 => [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04,
      0x02, 0x01, 0x05, 0x00, 0x04, 0x20]
  | .sha384 => [0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04,
      0x02, 0x02, 0x05, 0x00, 0x04, 0x30]
  | .sha512 => [0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04,
      0x02, 0x03, 0x05, 0x00, 0x04, 0x40]
  | .sha512_224 => [0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
      0x04, 0x02, 0x05, 0x05, 0x00, 0x04, 0x1c]
  | .sha512_256 => [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
      0x04, 0x02, 0x06, 0x05, 0x00, 0x04, 0x20]
  | .sha3_224 => [0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
      0x04, 0x02, 0x07, 0x05, 0x00, 0x04, 0x1c]
  | .sha3_256 => [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
      0x04, 0x02, 0x08, 0x05, 0x00, 0x04, 0x20]
  | .sha3_384 => [0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
      0x04, 0x02, 0x09, 0x05, 0x00, 0x04, 0x30]
  | .sha3_512 => [0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
      0x04, 0x02, 0x0a, 0x05, 0x00, 0x04, 0x40]

/-- `T`, the DER encoding of the `DigestInfo` of the hash value `H`
(§9.2 step 2, note 1). -/
def digestInfo (h : Hash) (H : List Byte) : List Byte := h.prefix ++ H

/-- EMSA-PKCS1-v1_5-ENCODE (§9.2) of the hash value `H` to `emLen` octets,
steps 2–6: `0x00 ‖ 0x01 ‖ PS ‖ 0x00 ‖ T`, with `PS` the `emLen - tLen - 3`
octets `0xff`; or `none` if `emLen < tLen + 11` ("intended encoded message
length too short", step 3) or `H` is not `hLen` octets (it is no value of
the hash: BoringSSL's `rsa_check_digest_size` refuses it). -/
def encode (h : Hash) (H : List Byte) (emLen : Nat) : Option (List Byte) :=
  let T := digestInfo h H
  if H.length ≠ h.len ∨ emLen < T.length + 11 then none
  else some ([0x00, 0x01] ++ List.replicate (emLen - T.length - 3) 0xff ++ [0x00] ++ T)

/-- BoringSSL's `RSA_padding_check_PKCS1_type_1` of the encoded message
`EM`: what follows `0x00 ‖ 0x01 ‖ PS ‖ 0x00`, where `PS` is all the octets
`0xff` after the first two (at least 8 of them), or `none` if `EM` does not
start with `0x00 0x01`, an octet other than `0xff` follows them before the
first `0x00`, there is no `0x00`, or `PS` has fewer than 8 octets. -/
def unpad : List Byte → Option (List Byte)
  | a :: b :: rest =>
    let ps := rest.takeWhile (· == 0xff)
    match rest.dropWhile (· == 0xff) with
    | c :: t => if a = 0x00 ∧ b = 0x01 ∧ c = 0x00 ∧ 8 ≤ ps.length then some t else none
    | [] => none
  | _ => none

/-- RSASSA-PKCS1-V1_5-VERIFY (§8.2.2) of the signature `sig` of the hash
value `H` with the public key `(nB, eB)`, as BoringSSL's
`rsa_verify_no_self_test` computes it: `sig` must be `k` octets (step 1),
RSAVP1 must succeed (step 2: the key is valid, `publicOpChecked`, and
`s < n`),
and what follows the padding of the result (`unpad`) must be exactly the
`DigestInfo` of `H`, which must be `hLen` octets. -/
def verify (nB eB : List Byte) (h : Hash) (H sig : List Byte) : Bool :=
  if sig.length = nB.length ∧ H.length = h.len then
    match publicOpChecked nB eB sig with
    | some em => unpad em == some (digestInfo h H)
    | none => false
  else false

/-- RSASSA-PKCS1-V1_5-VERIFY (§8.2.2) as written: step 1, the length of
`sig`; step 2, RSAVP1 and I2OSP to `k` octets (`publicOpChecked`); step 3, the
encoding `EM'` of `H` to `k` octets; step 4, `EM = EM'`. -/
def verifyRfc (nB eB : List Byte) (h : Hash) (H sig : List Byte) : Bool :=
  if sig.length = nB.length then
    match publicOpChecked nB eB sig, encode h H nB.length with
    | some em, some em' => em == em'
    | _, _ => false
  else false

/-- The hash value a signature `sig` signs with the public key `(nB, eB)`
and the hash `h`, as BoringSSL's `pkey_rsa_verify_recover` returns it: if
`sig` is `k` octets, RSAVP1 succeeds and the padding is valid (`unpad`),
and what follows it is `tLen` octets of which all but the last `hLen` are
the hash's prefix, those last `hLen` octets; otherwise `none`. -/
def recover (nB eB : List Byte) (h : Hash) (sig : List Byte) : Option (List Byte) :=
  if sig.length = nB.length then
    match publicOpChecked nB eB sig with
    | some em =>
      match unpad em with
      | some t =>
        if t.length = h.prefix.length + h.len ∧ t.take h.prefix.length = h.prefix then
          some (t.drop h.prefix.length)
        else none
      | none => none
    | none => none
  else none

/-- RSASSA-PKCS1-V1_5-SIGN (§8.2.1) of the hash value `H` with the private
key `(p, q, dP, dQ, qInv)` of the public key `(nB, eB)`: step 1,
EMSA-PKCS1-v1_5-ENCODE to `k` octets (`invalid` if it fails: `H` is not
`hLen` octets, or `k < tLen + 11`, "RSA modulus too short"); step 2, RSASP1
and I2OSP to `k` octets, checked against `e` (`privateChecked`: `invalid`
if the key or the encoding is refused, `fault` if the result fails the
check, which releases nothing). -/
def sign (nB eB pB qB dPB dQB qInvB : List Byte) (h : Hash) (H : List Byte) : Outcome :=
  match encode h H nB.length with
  | some em => privateChecked nB eB em pB qB dPB dQB qInvB
  | none => .invalid

end VG.Spec.RsaPkcs1Sig
