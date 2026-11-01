module

public import VerifiedGarbage.Proof.MlDsa.CanonicalizeContract

/-!
# ML-DSA: the contract of the response `z` and its norm

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

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

end VG.Proof.MlDsa
