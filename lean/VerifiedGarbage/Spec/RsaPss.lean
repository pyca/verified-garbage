import VerifiedGarbage.Spec.Mgf1

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1)

**Trusted** (as every file in `Spec/`). The signature scheme RSASSA-PSS of
PKCS #1 v2.2 (RFC 8017): its encoding method EMSA-PSS (§9.1), with the hash
function `H` and the mask generation function MGF1 (Appendix B.2.1) with the
hash function `G`, its signature operation (§8.1.1) with the private key,
and its verification operation (§8.1.2) with the public key `(n, e)`. Any
of the library's hash functions (`Mgf1.hashes`) may be either.

As in BoringSSL (`RSA_sign_pss_mgf1`, `RSA_verify_pss_mgf1`), the message is
given as its digest `mHash = Hash(M)` (§9.1.1 step 2, §9.1.2 step 2), which
must be `hLen` octets, and the salt is an input to the encoding: the caller
generates it (§9.1.1 step 4), with the salt length a convention chooses
(`SaltLength`).

Verification recovers the salt as BoringSSL's `RSA_verify_PKCS1_PSS_mgf1`
(`crypto/fipsmodule/rsa/padding.cc.inc`) does. Its step 10 takes `DB` to be
zeros, an octet `0x01` and the salt, finding the `0x01` as the first nonzero
octet, and then checks the salt's length if one is expected. For an expected
salt length `sLen` this accepts exactly what RFC 8017's step 10 accepts (the
leftmost `emLen - hLen - sLen - 2` octets of `DB` zero and the next `0x01`);
with no expected length (BoringSSL's `RSA_PSS_SALTLEN_AUTO`), which RFC 8017
does not have, it accepts a salt of any length, and step 3 checks only
`emLen ≥ hLen + 2`.

The modulus `n` has `modBits` bits, and EMSA-PSS encodes into `emBits =
modBits - 1` bits, `emLen = ⌈emBits / 8⌉` octets, which is the modulus'
length `k` or, if `modBits - 1` is a multiple of 8, `k - 1`. The integer
`OS2IP(EM)` is below `2^emBits`, hence below `n`, and as `k` octets
(`encodeK`) it is the input of RSASP1; RSAVP1 gives `k` octets, whose first
`k - emLen` must be zero (I2OSP's error in §8.1.2 step 2.c).

Signing (§8.1.1) is the private-key operation on `encodeK`, checked against
the public exponent as BoringSSL checks every private-key operation
(`Rsa.privateChecked`): the signature is released only if RSAVP1 takes it
back to the encoding. Verification takes the public key within BoringSSL's
limits (`Rsa.publicOpChecked`).
-/

namespace VG.Spec.RsaPss

open Mgf1 (Hash xorBytes mgf1)
open Rsa (os2ip publicOpChecked privateChecked Outcome)

/-- `n` zero octets. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- The number of bits of `n > 0`: `modBits`. -/
def bitLength (n : Nat) : Nat := Nat.log2 n + 1

/-- `emLen = ⌈emBits / 8⌉`. -/
def emLength (emBits : Nat) : Nat := (emBits + 7) / 8

/-- The octet string `bs` with its leftmost `z ≤ 7` bits set to zero (§9.1.1
step 11, §9.1.2 step 9, with `z = 8 emLen - emBits`). -/
def clearTop (z : Nat) : List Byte → List Byte
  | [] => []
  | b :: bs => (b &&& ((0xFF : Byte) >>> z)) :: bs

/-! ## Salt lengths -/

/-- A salt length convention, as BoringSSL's `salt_len`: a length, the
digest length (`RSA_PSS_SALTLEN_DIGEST`), or, as BoringSSL's
`RSA_PSS_SALTLEN_AUTO`, the longest salt when signing and any salt when
verifying. -/
inductive SaltLength
  | fixed (sLen : Nat)
  | digest
  | auto

/-- The salt length to sign with, for the hash function `H` and an encoding
of `emLen` octets: BoringSSL's `RSA_padding_add_PKCS1_PSS_mgf1`, whose `auto`
is `emLen - hLen - 2`, the longest that fits. -/
def SaltLength.sign (H : Hash) (emLen : Nat) : SaltLength → Nat
  | .fixed sLen => sLen
  | .digest => H.len
  | .auto => emLen - H.len - 2

/-- The salt length verification expects, for the hash function `H`, or
`none` for any (`auto`): BoringSSL's `RSA_verify_PKCS1_PSS_mgf1`. -/
def SaltLength.verify (H : Hash) : SaltLength → Option Nat
  | .fixed sLen => some sLen
  | .digest => some H.len
  | .auto => none

/-! ## EMSA-PSS (§9.1) -/

variable (H G : Hash)

/-- `EMSA-PSS-ENCODE` (§9.1.1) of the digest `mHash` with the salt `salt`,
into `emBits` bits, with the hash function `H` and MGF1 with `G`: `EM`, of
`emLen` octets, or `none` (an encoding error) if `mHash` is not `hLen`
octets or `emLen < hLen + sLen + 2`. -/
def encode (mHash salt : List Byte) (emBits : Nat) : Option (List Byte) :=
  let emLen := emLength emBits
  -- Steps 2 and 3.
  if mHash.length ≠ H.len ∨ emLen < H.len + salt.length + 2 then none else
    -- Steps 5 and 6.
    let h := H.hash (zeros 8 ++ mHash ++ salt)
    -- Steps 7 and 8.
    let db := zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt
    -- Steps 9–11.
    let maskedDB := clearTop (8 * emLen - emBits) (xorBytes db (mgf1 G h (emLen - H.len - 1)))
    -- Step 12.
    some (maskedDB ++ h ++ [0xbc])

/-- `EMSA-PSS-VERIFY` (§9.1.2) of the encoding `em` of `emBits` bits for the
digest `mHash`, with the hash function `H` and MGF1 with `G`, expecting the
salt length `sLen` (or any, if `none`), with BoringSSL's step 10: whether it
is consistent. -/
def verifyEncoding (mHash em : List Byte) (emBits : Nat) (sLen : Option Nat) : Bool :=
  let emLen := emLength emBits
  let z := 8 * emLen - emBits
  -- Steps 2 and 3, and that `em` is `emLen` octets.
  if mHash.length ≠ H.len ∨ em.length ≠ emLen ∨ emLen < H.len + sLen.getD 0 + 2 then false
  -- Step 4.
  else if em.getLast? ≠ some 0xbc then false
  else
    -- Step 5.
    let maskedDB := em.take (emLen - H.len - 1)
    let h := (em.drop (emLen - H.len - 1)).take H.len
    -- Step 6.
    if clearTop z maskedDB ≠ maskedDB then false
    else
      -- Steps 7–9.
      let db := clearTop z (xorBytes maskedDB (mgf1 G h (emLen - H.len - 1)))
      -- Steps 10 and 11, as BoringSSL: zeros, `0x01`, then the salt.
      match db.dropWhile (· == 0) with
      | 0x01 :: salt =>
        -- Steps 12–14.
        sLen.all (· == salt.length) && H.hash (zeros 8 ++ mHash ++ salt) == h
      | _ => false

/-! ## RSASSA-PSS (§8.1) -/

/-- The encoding of the digest `mHash` with the salt `salt` for the modulus
`nB` (`k` octets), as `k` octets: §8.1.1 step 1's `EM = EMSA-PSS-ENCODE(M,
modBits - 1)`, then `m = OS2IP(EM)` as `k` octets, the input of RSASP1
(step 2.a–b); or `none` if the encoding fails. -/
def encodeK (nB mHash salt : List Byte) : Option (List Byte) :=
  let emBits := bitLength (os2ip nB) - 1
  (encode H G mHash salt emBits).map (zeros (nB.length - emLength emBits) ++ ·)

/-- `RSASSA-PSS-VERIFY((n, e), M, S)` (§8.1.2) of the signature `sB` for the
digest `mHash`, with the public key `(nB, eB)`, the hash function `H` and
MGF1 with `G`, expecting the salt length `sLen` (or any, if `none`): whether
the signature is valid. Step 1: `sB` is `k` octets; step 2: RSAVP1, and
`EM = I2OSP(m, emLen)`, which requires the first `k - emLen` octets of `m`
to be zero; step 3: `EMSA-PSS-VERIFY`. RSAVP1 is `publicOpChecked`, within
BoringSSL's limits on the public key (`rsa_check_public_key`). -/
def verify (nB eB mHash sB : List Byte) (sLen : Option Nat) : Bool :=
  let k := nB.length
  let emBits := bitLength (os2ip nB) - 1
  let emLen := emLength emBits
  sB.length == k &&
    match publicOpChecked nB eB sB with
    | some x => x.take (k - emLen) == zeros (k - emLen) &&
        verifyEncoding H G mHash (x.drop (k - emLen)) emBits sLen
    | none => false

/-- `RSASSA-PSS-SIGN(K, M)` (§8.1.1) of the digest `mHash` with the salt
`salt`, with the private key `(p, q, dP, dQ, qInv)` of the modulus `nB` and
the public exponent `eB`, the hash function `H` and MGF1 with `G`: step 1,
`encodeK`, then step 2, RSASP1 checked against `e` (`privateChecked`). The
outcome is `ok` with the signature (`k` octets), `invalid` if the encoding
fails or `privateChecked` refuses the key, or `fault` (the internal error)
if the result fails the check against `e`. -/
def sign (nB eB pB qB dPB dQB qInvB mHash salt : List Byte) : Outcome :=
  match encodeK H G nB mHash salt with
  | some em => privateChecked nB eB em pB qB dPB dQB qInvB
  | none => .invalid

end VG.Spec.RsaPss
