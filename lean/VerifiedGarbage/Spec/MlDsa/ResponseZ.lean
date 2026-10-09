import VerifiedGarbage.Spec.MlDsa.Canonicalize

namespace VG.Spec.MlDsa

/-- The signed inverse-transform range, without fixing a represented polynomial. -/
def RawReduced (m : Mem) (p : Addr) : Prop :=
  ∀i<n,-(q:Int)<(coeffAt m p i).toInt ∧ (coeffAt m p i).toInt<2*(q:Int)

def addNormSig : Sig where
  params := [("y",.array true .u32 256),("cs",.array false .u32 256),("bound",.int .u32 true)]
  ret := some .u32

/-- Fused response addition and norm check. Signed output is written on both
acceptance and rejection; the return value is the exact polynomial norm test. -/
def addNormContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  addNormSig.contract A
    (pre := fun y cs bound m => Reduced m y ∧ RawReduced m cs ∧ 1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun y cs bound m m' r =>
      CenteredReduced m' y ∧ signedPolyAt m' y=add (polyAt m y) (signedPolyAt m cs) ∧
      r=if normRq [add (polyAt m y) (signedPolyAt m cs)]<bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

def addNormApi : Api where
  module := "mldsa"
  name := "vg_mldsa_signed_add_norm"
  sig := addNormSig
  writeArgs := true
  contracts := some fun A stack => addNormContract A stack
  summary := "Adds a canonical polynomial and a signed inverse-transform result, returning signed coefficients and the strict norm-check result."
  safety := ["The first input must be canonical modulo 8380417; the second must have signed coefficients strictly between -8380417 and 16760834.",
    "The norm bound must be between 1 and 524288 inclusive."]

end VG.Spec.MlDsa
