module

public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract

/-!
# ML-DSA: the contract of a Montgomery-scaled product

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

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

end VG.Proof.MlDsa
