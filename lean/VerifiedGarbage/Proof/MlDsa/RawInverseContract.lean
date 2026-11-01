module

public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract

/-!
# ML-DSA: the contract of a fused product and inverse transform with signed output

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

Signed output for the internal fused multiplication/inverse helper.
The canonical fused interface remains separate and unchanged.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Interpret each stored 32-bit coefficient as a signed integer modulo q. -/
def signedPolyAt (m : Mem) (p : Addr) : Poly :=
  Vector.ofFn fun i => ofInt (coeffAt m p i.val).toInt

/-- The strict Barrett output interval and its represented field polynomial. -/
def RawPolyIs (m : Mem) (p : Addr) (f : Poly) : Prop :=
  (∀ i<n, -(q : Int)<(coeffAt m p i).toInt ∧ (coeffAt m p i).toInt<2*(q : Int)) ∧
    signedPolyAt m p=f

def multiplyInverseRawSig : Sig := multiplyInverseSig

def multiplyInverseRawContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  multiplyInverseRawSig.contract A
    (pre := fun _out a b _scratch m => PositiveReduced m a ∧ PositiveReduced m b)
    (post := fun out a b _scratch m m' _ =>
      RawPolyIs m' out (nttInv (multiplyNTT (polyAt m a) (polyAt m b))))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa
