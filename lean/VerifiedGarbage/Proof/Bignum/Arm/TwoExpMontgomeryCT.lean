module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpKernelCT

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

theorem MontgomeryTiming.kernelTiming {base : BitVec 32} {len w : Nat}
    {P : State → Prop} {regions : List Region} {A : Montgomery base len w P regions}
    (ct : MontgomeryTiming A) (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) : Timing A.kernel := by
  apply timing_of_square A.kernel rfl fit hn
  exact (ct.op_ct 6 6 6
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])).mono
    (fun _ _ h => by
      obtain ⟨⟨M1, E1, p1, q1⟩, ⟨M2, E2, p2, q2⟩, sp⟩ := h
      exact ⟨⟨p1.ready, q1, by rw [p1.modulus]; exact p1.bound⟩,
        ⟨p2.ready, q2, by rw [p2.modulus]; exact p2.bound⟩, sp⟩)
    (fun _ _ h => h)

end VG.Proof.Bignum.Arm.TwoExp
