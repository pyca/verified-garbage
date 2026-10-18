module

public import VerifiedGarbage.Spec.MlDsa.ResponseZ

@[expose] public section

namespace VG.Spec.MlDsa

/-- The field difference of a canonical coefficient and a signed coefficient. -/
def responseDifference (m : Mem) (w cs : Addr) (i : Nat) : Zq :=
  ofInt (((coeffAt m w i).toNat:Int)-(coeffAt m cs i).toInt)

def responseLowPass (m : Mem) (w cs : Addr) (g B : Nat) : Prop :=
  ∀i<n,normZq (ofInt (lowBits g (responseDifference m w cs i)))<B

instance (m : Mem) (w cs : Addr) (g B : Nat) : Decidable (responseLowPass m w cs g B) :=
  Nat.decidableBallLT n (fun i _ => normZq (ofInt (lowBits g (responseDifference m w cs i)))<B)

def subLowNormSig : Sig where
  params := [("w",.array true .u32 256),("cs",.array false .u32 256),
    ("low",.array true .u32 256),("gamma2",.int .u32 true),("bound",.int .u32 false)]
  ret := some .u32

/-- Decompose the difference and check its low-part norm. Both outputs are exact
on acceptance and rejection; low coefficients are stored as signed integers. -/
def subLowNormContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  subLowNormSig.contract A
    (pre := fun w cs _low gamma2 bound m => Reduced m w ∧ RawReduced m cs ∧
      gamma2.toNat∈gamma2s ∧ 1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun w cs low gamma2 bound m m' r =>
      (∀i<n,(coeffAt m' w i).toNat=(highBits gamma2.toNat (responseDifference m w cs i)).toNat) ∧
      (∀i<n,(coeffAt m' low i).toInt=lowBits gamma2.toNat (responseDifference m w cs i)) ∧
      r=if responseLowPass m w cs gamma2.toNat bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

end VG.Spec.MlDsa
