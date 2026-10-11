module

public import VerifiedGarbage.Spec.MlDsa.FusedInverse
public import VerifiedGarbage.Spec.MlDsa.Montgomery

@[expose] public section

namespace VG.Spec.MlDsa

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

def montDotApi (count : Nat) : Api where
  module := "mldsa"
  name := "vg_mldsa_montgomery_dot"++toString count
  sig := montDotSig count
  writeArgs := true
  contracts := some fun A stack=>montDotContract A count stack
  summary := "Writes the canonical sum of coefficientwise polynomial products, scaled by the inverse of 2^32 modulo q."
  safety := ["All coefficients in both input families must be less than 25141251 (3q)."]

end VG.Spec.MlDsa
