module

public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract

/-!
# ML-DSA: the contract of Montgomery-scaled dot products

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- A canonical Montgomery-scaled sum, before the caller subtracts another
Montgomery product and performs the inverse transform. -/
def montDotSig (count : Nat) : Sig where
  params := [("out",.array true .u32 256),("a",.array false .u32 (256*count)),
    ("b",.array false .u32 (256*count))]

def montDotContract {M : ISA} (A : Abi M) (count : Nat) (stack : Nat := 0) : Contract M :=
  (montDotSig count).contract A
    (pre := fun _out a b m =>
      (∀j<count,PositiveReduced m (a+BitVec.ofNat 64 (1024*j))) ∧
      (∀j<count,PositiveReduced m (b+BitVec.ofNat 64 (1024*j))))
    (post := fun out a b m m' _ => PolyIs m' out
      ((dotNTT
        (fun j=>polyAt m (a+BitVec.ofNat 64 (1024*j)))
        (fun j=>polyAt m (b+BitVec.ofNat 64 (1024*j))) count).map (· * montgomeryRInv)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa
