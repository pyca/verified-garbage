module

public import VerifiedGarbage.Spec.Hmac

/-!
# HKDF (RFC 5869)

**Trusted** (as every file in `Spec/`). The HMAC-based extract-and-expand
key derivation function HKDF, over any hash function with an input block
size, transcribed from RFC 5869, *HMAC-based Extract-and-Expand Key
Derivation Function (HKDF)* (May 2010), §2.2 (HKDF-Extract) and §2.3
(HKDF-Expand), with HMAC as `Spec/Hmac.lean` has it. Salts, input keying
material, pseudorandom keys, context information and output keying material
are sequences of bytes.

The contracts of the functions that compute them, with the hash function
given at run time as a table of HMAC over it, are in `Spec/Hkdf/Table.lean`.
-/

@[expose] public section

namespace VG.Spec.Hkdf

variable (H : Hmac.HashFunction)

/-- `HKDF-Extract(salt, IKM) = HMAC-Hash(salt, IKM)` (§2.2): the
pseudorandom key `PRK`. RFC 5869 takes a salt that is not provided to be
`HashLen` zero octets; this takes the salt as given, so a caller without one
passes those octets (or the empty salt, which HMAC pads with zeros to the
same key, FIPS 198-1 §4 step 3). -/
def extract (salt ikm : List Byte) : List Byte := Hmac.hmac H salt ikm

/-- `n` more octet strings of HKDF-Expand's `T` (§2.3), from `T(i - 1) =
prev` and the counter `i`: `T(i) = HMAC-Hash(PRK, T(i - 1) ‖ info ‖ i)`, with
`i` a single octet, then those after it, concatenated. -/
def blocks (prk info : List Byte) : Nat → List Byte → Nat → List Byte
  | 0, _, _ => []
  | n + 1, prev, i =>
    let t := Hmac.hmac H prk (prev ++ info ++ [BitVec.ofNat 8 i])
    t ++ blocks prk info n t (i + 1)

/-- `HKDF-Expand(PRK, info, L)` (§2.3), for a hash function with outputs of
`hashLen` octets: `none` if `L` is more than `255 · HashLen`; otherwise the
first `L` octets of `T = T(1) ‖ T(2) ‖ … ‖ T(N)`, where
`N = ceil(L / HashLen)` and `T(0)` is the empty string. -/
def expand (hashLen : Nat) (prk info : List Byte) (len : Nat) : Option (List Byte) :=
  if 255 * hashLen < len then none
  else some ((blocks H prk info ((len + hashLen - 1) / hashLen) [] 1).take len)

end VG.Spec.Hkdf
