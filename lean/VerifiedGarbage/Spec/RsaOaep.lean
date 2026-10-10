module

public import VerifiedGarbage.Spec.Mgf1

/-!
# RSAES-OAEP (RFC 8017 §7.1, EME-OAEP)

**Trusted** (as every file in `Spec/`). The encryption scheme RSAES-OAEP of
PKCS #1 v2.2 (RFC 8017): its encoding method EME-OAEP (§7.1.1 step 2,
§7.1.2 step 3), with the hash function `H` (for the label) and the mask
generation function MGF1 (Appendix B.2.1) with the hash function `G`, and its
encryption operation (§7.1.1) with the public key `(n, e)`, within
BoringSSL's limits (`Rsa.publicOpChecked`), and its decryption operation
(§7.1.2) with the private key, checked against the public exponent as
BoringSSL checks every private-key operation (`Rsa.privateChecked`). Any of
the library's hash functions (`Mgf1.hashes`) may be either.

The seed is an input to encryption: the caller generates it, `hLen` random
octets (§7.1.1 step 2.d).

Decoding is BoringSSL's `RSA_padding_check_PKCS1_OAEP_mgf1`
(`crypto/rsa/rsa_crypt.cc`), which is RFC 8017's step 3: `EM` is
`Y ‖ maskedSeed ‖ maskedDB`, unmasked into `DB = lHash' ‖ PS ‖ 0x01 ‖ M`, and
it fails if `Y` is not zero, `lHash'` is not the label's hash, or no `0x01`
follows the zeros after `lHash'`. Every failure is the same one, `none`
(§7.1.2 step 3.g: "the opponent [must] not be able to distinguish the error
conditions"); BoringSSL computes all three conditions in constant time and
only then reveals whether decoding failed.

The encoding is `k` octets, the modulus' length: its first octet is zero, so
as an integer it is below `256^(k-1)`, hence below `n`.
-/

@[expose] public section

namespace VG.Spec.RsaOaep

open Mgf1 (Hash xorBytes mgf1)
open Rsa (publicOpChecked privateChecked Outcome)

/-- `n` zero octets. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

variable (H G : Hash)

/-- EME-OAEP encoding (§7.1.1 step 2) of the message `m` with the label
`label` and the seed `seed`, into `k` octets, with the hash function `H` and
MGF1 with `G`: `EM`, or `none` if the seed is not `hLen` octets, `k < 2 hLen
+ 2`, or the message is longer than `k - 2 hLen - 2` octets (step 1.b).

Step 1.a's limit on the label's length, which no label here reaches, is left
out. -/
def encode (label m seed : List Byte) (k : Nat) : Option (List Byte) :=
  if seed.length ≠ H.len ∨ k < 2 * H.len + 2 + m.length then none else
    -- Steps 2.a–c.
    let db := H.hash label ++ zeros (k - m.length - 2 * H.len - 2) ++ 0x01 :: m
    -- Steps 2.e–h.
    let maskedDB := xorBytes db (mgf1 G seed (k - H.len - 1))
    let maskedSeed := xorBytes seed (mgf1 G maskedDB H.len)
    -- Step 2.i.
    some (0x00 :: maskedSeed ++ maskedDB)

/-- EME-OAEP decoding (§7.1.2 step 3) of `em` (`k` octets) with the label
`label`, with the hash function `H` and MGF1 with `G`: the message, or
`none` (the decryption error) if `k < 2 hLen + 2` or the encoding is not
valid. -/
def decode (label em : List Byte) : Option (List Byte) :=
  let k := em.length
  if k < 2 * H.len + 2 then none else
    -- Step 3.b.
    let maskedSeed := (em.drop 1).take H.len
    let maskedDB := em.drop (H.len + 1)
    -- Steps 3.c–f.
    let seed := xorBytes maskedSeed (mgf1 G maskedDB H.len)
    let db := xorBytes maskedDB (mgf1 G seed (k - H.len - 1))
    -- Step 3.g: `Y = 0`, `lHash' = lHash`, and zeros then `0x01` after it.
    match (db.drop H.len).dropWhile (· == 0) with
    | 0x01 :: m => if em.take 1 = [0x00] ∧ db.take H.len = H.hash label then some m else none
    | _ => none

/-- `RSAES-OAEP-ENCRYPT((n, e), M, L)` (§7.1.1) of the message `m` with the
label `label` and the seed `seed`, with the public key `(nB, eB)`, the hash
function `H` and MGF1 with `G`: the ciphertext (`k` octets), or `none` if
encoding fails or the public key is not within BoringSSL's limits
(`publicOpChecked`). -/
def encrypt (nB eB label m seed : List Byte) : Option (List Byte) :=
  (encode H G label m seed nB.length).bind (publicOpChecked nB eB)

/-- `RSAES-OAEP-DECRYPT(K, C, L)` (§7.1.2) of the ciphertext `cB` with the
label `label`, with the private key `(p, q, dP, dQ, qInv)` of the modulus
`nB` and the public exponent `eB`, the hash function `H` and MGF1 with `G`:
step 1.b (`cB` is `k` octets), step 2, RSADP checked against `e`
(`privateChecked`), and step 3, `decode`. The outcome is `ok` with the
message, or `fault` (the internal error) if RSADP's result fails its check
against `e`; every other failure, of the length, the key, the ciphertext's
range or the decoding, is the single error `invalid` (§7.1.2's "decryption
error"). Step 1.c's check that `k ≥ 2 hLen + 2` is `decode`'s. -/
def decrypt (nB eB pB qB dPB dQB qInvB label cB : List Byte) : Outcome :=
  if cB.length ≠ nB.length then .invalid else
    match privateChecked nB eB cB pB qB dPB dQB qInvB with
    | .ok em =>
      match decode H G label em with
      | some m => .ok m
      | none => .invalid
    | .invalid => .invalid
    | .fault => .fault

end VG.Spec.RsaOaep
