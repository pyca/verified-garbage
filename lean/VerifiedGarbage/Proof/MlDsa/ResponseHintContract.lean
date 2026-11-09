module

public import VerifiedGarbage.Proof.MlDsa.ResponseZContract

/-!
# ML-DSA: the contract of the response hint and its norm

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Reconstruct the field coefficient represented by its signed low part and high part. -/
def responseHintBase (m : Mem) (low high : Addr) (g i : Nat) : Zq :=
  ofInt ((coeffAt m low i).toInt+2*(g:Int)*(coeffAt m high i).toNat)

/-- Inputs are an exact decomposition, including the special high-zero boundary. -/
def ResponseDecomposed (m : Mem) (low high : Addr) (g : Nat) : Prop :=
  ∀i<n,(coeffAt m low i).toInt=lowBits g (responseHintBase m low high g i) ∧
    (coeffAt m high i).toNat=(highBits g (responseHintBase m low high g i)).toNat

end VG.Proof.MlDsa
