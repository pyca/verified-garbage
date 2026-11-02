module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallOpCT

/-! # The shared arithmetic kernel supplies exponentiation's timing interface -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Rsa.Mont (Operand)

theorem sharedMontgomeryTiming (base sp : BitVec 32) (len w : Nat) (name : String) (callee : Prog isa)
    (correct : ∀ (o a b : Nat), Operand o → Operand a → Operand b →
      ∀ s, CallInput base len w o a b s →
        WP isa callee s fun t => abiPreserved s t ∧ CallResult base len w o a b s t)
    (stack : armStack callee ≤ 40)
    (ct : ∀ (o a b : Nat), Operand o → Operand a → Operand b →
      RelCT isa (fun s t => CallInput base len w o a b s ∧
        CallInput base len w o a b t ∧ s.sp = t.sp) callee (fun _ _ => True)) :
    MontgomeryTiming (sharedMontgomery base sp len w name callee correct stack) := by
  constructor
  intro o a b ho ha hb
  exact (montCallOp_ct name callee (ct o a b ho ha hb) ho ha hb).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.1.2.1.1, h.2.1.2.1.1,
      h.1.2.2, h.2.1.2.2, h.2.2⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm.TwoExp
