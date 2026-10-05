import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# The `DigestInfo` prefixes are DER encodings

A check of `Spec.RsaPkcs1Sig.Hash.prefix`, whose octets are transcribed from
RFC 8017 §9.2 note 1 (and OpenSSL for SHA-3), against an independent
construction: every prefix is the DER encoding (ITU-T X.690) of

```
DigestInfo ::= SEQUENCE {
    digestAlgorithm AlgorithmIdentifier,   -- SEQUENCE { OID, NULL }
    digest OCTET STRING                    -- hLen octets
}
```

up to the digest's octets, with the hash's object identifier given by its
arcs (`oid`): RFC 1321's `md5` 1.2.840.113549.2.5, `id-sha1`
1.3.14.3.2.26 (RFC 3279 §2.2.1), and NIST's `id-sha224` … `id-sha3-512`,
2.16.840.1.101.3.4.2.1 to .10 (RFC 5754 §2, NIST's Computer Security
Objects Register).
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.RsaPkcs1Sig

/-- The base-128 digits of `n` (X.690 §8.19.2), most significant first, with
the high bit set on all but the last; `fuel` bounds the digits. -/
def base128 : Nat → Nat → List Nat
  | 0, n => [n % 128]
  | fuel + 1, n => if n < 128 then [n] else (base128 fuel (n / 128)).map (· ||| 128) ++ [n % 128]

/-- The contents octets of an object identifier from its arcs
(X.690 §8.19): `40 a + b` for the first two, then each in base 128. -/
def oidContents : List Nat → List Byte
  | a :: b :: rest => ((40 * a + b) :: rest).flatMap (fun n => (base128 4 n).map (BitVec.ofNat 8))
  | _ => []

/-- A DER type-length-value with a short length (below 128). -/
def tlv (tag : Byte) (contents : List Byte) : List Byte :=
  [tag, BitVec.ofNat 8 contents.length] ++ contents

/-- The DER encoding of a `DigestInfo` with the algorithm `oid`, NULL
parameters and `hLen` octets of digest, but for those octets. -/
def digestInfoPrefix (oid : List Nat) (hLen : Nat) : List Byte :=
  let algId := tlv 0x30 (tlv 0x06 (oidContents oid) ++ tlv 0x05 [])
  [0x30, BitVec.ofNat 8 (algId.length + 2 + hLen)] ++ algId ++ [0x04, BitVec.ofNat 8 hLen]

/-- The arcs of each hash's object identifier. -/
def oid : Hash → List Nat
  | .md5 => [1, 2, 840, 113549, 2, 5]
  | .sha1 => [1, 3, 14, 3, 2, 26]
  | .sha256 => [2, 16, 840, 1, 101, 3, 4, 2, 1]
  | .sha384 => [2, 16, 840, 1, 101, 3, 4, 2, 2]
  | .sha512 => [2, 16, 840, 1, 101, 3, 4, 2, 3]
  | .sha224 => [2, 16, 840, 1, 101, 3, 4, 2, 4]
  | .sha512_224 => [2, 16, 840, 1, 101, 3, 4, 2, 5]
  | .sha512_256 => [2, 16, 840, 1, 101, 3, 4, 2, 6]
  | .sha3_224 => [2, 16, 840, 1, 101, 3, 4, 2, 7]
  | .sha3_256 => [2, 16, 840, 1, 101, 3, 4, 2, 8]
  | .sha3_384 => [2, 16, 840, 1, 101, 3, 4, 2, 9]
  | .sha3_512 => [2, 16, 840, 1, 101, 3, 4, 2, 10]

theorem prefix_eq (h : Hash) : h.prefix = digestInfoPrefix (oid h) h.len := by
  cases h <;> decide

/-- Every hash function has a number below 12. -/
theorem ofId_some (h : Hash) : ∃ i < 12, Hash.ofId i = some h := by
  cases h <;> decide

end VG.Proof.RsaPkcs1Sig
