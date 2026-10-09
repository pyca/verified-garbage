import VerifiedGarbage.Spec.MlDsa.FusedInverse

/-! Signed output for the internal fused multiplication/inverse helper.
The canonical fused interface remains separate and unchanged. -/
namespace VG.Spec.MlDsa

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

def multiplyInverseRawApi : Api where
  module := "mldsa"
  name := "vg_mldsa_multiply_inverse_raw"
  sig := multiplyInverseRawSig
  writeArgs := true
  contracts := some fun A stack => multiplyInverseRawContract A stack
  summary := "Multiplies two NTT polynomials and applies the inverse transform, returning signed representatives strictly between -q and 2q."
  safety := ["Each input coefficient must be less than 3q, where q = 8380417.",
    "Output coefficients are signed 32-bit representatives; they are not canonical residues."]

end VG.Spec.MlDsa
