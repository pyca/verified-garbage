module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979
public import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# Deterministic ECDSA over any curve with a fixed hash function

Not trusted: what the proofs of `vg_ecdsa_<curve>_sign` on each target state
their correctness with, for the hash function that the table names. An
`Instance` is a curve's `Ecdsa.Instance`, a hash function for HMAC, its
output length and the bound on candidates. `result` is RFC 6979's signature
(`Rfc6979.sign`) with it, of the hash `digest` (`hashLen` octets, the hash
function's output) with the private key `d` (`len` octets, most significant
first), and the number of candidates tried. The trusted contract,
`Spec/Ecdsa/Rfc6979/Table.lean`'s `TableInstance.signContract`, takes the
hash function at run time instead (`TableInstance.result`), which each
target's `tresult_eq` relates to this.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979

/-- A curve and a hash function for HMAC. -/
structure Instance where
  ecdsa : Spec.Ecdsa.Instance
  hash : Spec.Hmac.HashFunction
  /-- The length of the hash function's output, in octets. -/
  hashLen : Nat
  /-- The most candidates `sign` tries. -/
  tries : Nat
  /-- Working space in `u64`s. A wrapper may need space beyond the ECDSA
  core's 8 KiB to retain values across calls of that core. -/
  scratchWords : Nat := Spec.Ecdsa.scratchWords

namespace Instance

variable (I : Instance)

/-- RFC 6979's signature of `digest` with the private key `d`, and the
number of candidates tried. -/
def result (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  Spec.Ecdsa.Rfc6979.sign I.ecdsa.curve I.hash I.hashLen I.tries
    (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt m d I.ecdsa.curve.len))
    (Spec.Ecdsa.bytesAt m digest I.hashLen)

end Instance

end VG.Proof.Ecdsa.Rfc6979
