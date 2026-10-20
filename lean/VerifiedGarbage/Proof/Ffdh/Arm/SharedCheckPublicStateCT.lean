module

public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMainCT
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory

/-! Persistent call memory accompanies the existing public-value timing states. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure SharedSubgroupInput (p : Inputs) (slots : List Nat) (slot : Nat) (bb : List Byte)
    (s : State) : Prop extends SubgroupInput p slots slot bb s where
  calls : DomainCallMemory p s

structure SharedPublicMainInput (p : Inputs) (slots : List Nat) (yb : List Byte)
    (s : State) : Prop extends PublicMainInput p slots yb s where
  calls : DomainCallMemory p s

structure SharedPublicImported (p : Inputs) (slots : List Nat) (yb : List Byte)
    (s : State) : Prop extends PublicImported p slots yb s where
  calls : DomainCallMemory p s

structure SharedPublicRanged (p : Inputs) (slots : List Nat) (yb : List Byte)
    (s : State) : Prop extends PublicRanged p slots yb s where
  calls : DomainCallMemory p s

end VG.Proof.Ffdh.Arm
