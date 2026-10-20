module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.KeyGeneration

/-! The shared key-attempt contract, stated at the current entropy-tape offset. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh
open VG.Proof.Ffdh.KeyGeneration

def keyRand (p : KeyPublic) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr p.rp) p.randLen

abbrev KeyPublic.tail (p : KeyPublic) (rand : List Byte) (used keys scalars : Nat) : KeySearchResult :=
  keyTail p.a p.len rand used keys scalars

abbrev sampledScalar (p : KeyPublic) (original : State) (used : Nat) : Nat :=
  scalarOfOctets p.a (((keyRand p original).drop used).take p.len)

abbrev currentStatus (p : KeyPublic) (original : State) (used : Nat) : Nat :=
  attemptStatus p.a p.len ((keyRand p original).drop used)

structure AttemptPost (p : KeyPublic) (original : State) (used : Nat) (s : State) : Prop where
  status : (s.gpr .r0).toNat = currentStatus p original used
  output : if currentStatus p original used = 1 then
    Spec.Rsa.bytesAt s.mem (State.addr p.xp) p.len = Spec.Rsa.i2osp (sampledScalar p original used) p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.yp) p.len =
        Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g (sampledScalar p original used) p.a.p) p.len
    else Spec.Rsa.bytesAt s.mem (State.addr p.xp) p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.yp) p.len = List.replicate p.len 0

def acceptedResult (p : KeyPublic) (original : State) (used : Nat) : KeySearchResult :=
  ⟨.accepted (sampledScalar p original used) (Spec.Rsa.powMod p.a.g (sampledScalar p original used) p.a.p),
    used + p.len, [1]⟩

theorem currentStatus_cases (p : KeyPublic) (original : State) (used : Nat) :
    currentStatus p original used = 1 ∨ currentStatus p original used = 2 ∨
      currentStatus p original used = 3 :=
  attemptStatus_cases _ _ _

end VG.Proof.Ffdh.Arm.KeySearch
