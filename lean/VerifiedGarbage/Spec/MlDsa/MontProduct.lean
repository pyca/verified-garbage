module

public import VerifiedGarbage.Spec.MlDsa.FusedInverse
public import VerifiedGarbage.Spec.MlDsa.Montgomery

@[expose] public section

namespace VG.Spec.MlDsa

def montProductSig : Sig where
  params := [("out",.array true .u32 256),("a",.array false .u32 256),
    ("b",.array false .u32 256)]

/-- Canonical Montgomery product of two positive NTT representations. -/
def montProductContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  montProductSig.contract A
    (pre := fun _out a b m => PositiveReduced m a ∧ PositiveReduced m b)
    (post := fun out a b m m' _ =>
      PolyIs m' out (montgomeryMultiplyNTT (polyAt m a) (polyAt m b)))
    (writeArgs := true) (stack := stack)

def montProductApi : Api where
  module := "mldsa"
  name := "vg_mldsa_montgomery_product"
  sig := montProductSig
  writeArgs := true
  contracts := some fun A stack => montProductContract A stack
  summary := "Multiplies two positive NTT polynomials with the Montgomery factor R inverse, returning canonical coefficients."
  safety := ["Each input coefficient must be less than 3q, where q = 8380417."]

end VG.Spec.MlDsa
