module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979
public import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# Deterministic ECDSA over any curve with a fixed hash function

**Trusted** (as every file in `Spec/`). An `Instance` is a curve's
`Ecdsa.Instance`, a hash function for HMAC, its output length and the bound
on candidates. `result` is RFC 6979's signature (`Rfc6979.sign`) with it, of
the hash `digest` (`hashLen` octets, the hash function's output) with the
private key `d` (`len` octets, most significant first), and the number of
candidates tried. The contract of `vg_ecdsa_<curve>_sign`
(`Spec/Ecdsa/Rfc6979/Table.lean`) takes the hash function at run time
instead (`TableInstance.result`).
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979

open Weierstrass

/-- A curve and a hash function for HMAC. -/
structure Instance where
  ecdsa : Ecdsa.Instance
  hash : Hmac.HashFunction
  /-- The length of the hash function's output, in octets. -/
  hashLen : Nat
  /-- The most candidates `sign` tries. -/
  tries : Nat
  /-- Working space in `u64`s. A wrapper may need space beyond the ECDSA
  core's 8 KiB to retain values across calls of that core. -/
  scratchWords : Nat := Ecdsa.scratchWords

namespace Instance

variable (I : Instance)

/-- RFC 6979's signature of `digest` with the private key `d`, and the
number of candidates tried. -/
def result (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  sign I.ecdsa.curve I.hash I.hashLen I.tries (ofBytes (bytesAt m d I.ecdsa.curve.len))
    (bytesAt m digest I.hashLen)

end Instance

end VG.Spec.Ecdsa.Rfc6979
