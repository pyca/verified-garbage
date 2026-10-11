module

public import VerifiedGarbage.Spec.MlDsa.RawInverse

@[expose] public section

namespace VG.Spec.MlDsa

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

def canonicalizeApi : Api where
  module := "mldsa"
  name := "vg_mldsa_canonicalize_signed"
  sig := canonicalizeSig
  writeArgs := true
  contracts := some fun A stack => canonicalizeContract A stack
  summary := "Converts 256 signed polynomial coefficients to canonical residues modulo q, preserving their field values."
  safety := ["Each coefficient, interpreted as a signed 32-bit integer, must be strictly between -8380417 and 8380417."]

end VG.Spec.MlDsa
