module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallOp

/-! # Generator-two exponentiation calls one shared arithmetic kernel -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

abbrev CallReady (base sp : BitVec 32) (len : Nat) (s : State) : Prop :=
  CallStack base len s ∧ s.sp = sp

def sharedMontgomery (base sp : BitVec 32) (len w : Nat) (name : String) (callee : Prog isa)
    (correct : ∀ (o a b : Nat), Operand o → Operand a → Operand b →
      ∀ s, CallInput base len w o a b s →
        WP isa callee s fun t => abiPreserved s t ∧ CallResult base len w o a b s t)
    (stack : armStack callee ≤ 40) :
    Montgomery base len w (CallReady base sp len)
      [⟨State.addr base, 8 * len⟩, belowA sp 48] where
  op := MontCall.op name callee
  workspace := by simp
  stable := by
    intro s t _ rest h
    exact ⟨h.1.of_rest rest, rest.sp.trans h.2⟩
  op_ok := by
    intro s o a b h hp ho ha hb ho0 operand
    refine WP.mono (montCallOp_ok name callee (correct o a b ho ha hb) stack s h hp.1 ho ha hb ho0 operand) ?_
    rintro t ⟨ready, cs, modulus, bound, value, keeps, frame, rest⟩
    rw [hp.2] at frame
    exact ⟨ready, modulus, bound, value, keeps, ⟨cs, rest.sp.trans hp.2⟩, frame, rest⟩

end VG.Proof.Bignum.Arm.TwoExp
