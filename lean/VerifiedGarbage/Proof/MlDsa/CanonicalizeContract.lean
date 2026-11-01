module

public import VerifiedGarbage.Proof.MlDsa.RawInverseContract

/-!
# ML-DSA: the contract of canonicalizing signed coefficients

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Signed representatives accepted by the response norm check. -/
def CenteredReduced (m : Mem) (p : Addr) : Prop :=
  ∀i<n,-(q:Int)<(coeffAt m p i).toInt ∧ (coeffAt m p i).toInt<(q:Int)

def canonicalizeSig : Sig where
  params := [("f",.array true .u32 256)]

/-- Change only the stored representative, preserving the field polynomial. -/
def canonicalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  canonicalizeSig.contract A
    (pre := fun f m => CenteredReduced m f)
    (post := fun f m m' _ => PolyIs m' f (signedPolyAt m f))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa
