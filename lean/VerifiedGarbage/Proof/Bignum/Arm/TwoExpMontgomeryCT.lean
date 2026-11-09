module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

/-! # Timing interface for shared Montgomery calls -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)

abbrev OpInput (base : BitVec 32) (len w : Nat) (P : State → Prop) (b : Nat) (s : State) : Prop :=
  ArithmeticReady base len w s ∧ P s ∧
    numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0

structure MontgomeryTiming {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) : Prop where
  op_ct : ∀ (o a b : Nat), Operand o → Operand a → Operand b →
    RelCT isa (fun s t => OpInput base len w P b s ∧ OpInput base len w P b t ∧ s.sp = t.sp)
      (A.op o a b) (fun _ _ => True)

end VG.Proof.Bignum.Arm.TwoExp
