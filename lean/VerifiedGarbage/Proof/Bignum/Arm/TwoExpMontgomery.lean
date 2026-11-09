module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpKernel
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # Shared Montgomery operations used by generator-two exponentiation

This interface names calls rather than duplicating arithmetic bodies in
the initialization, bit loop, and final Montgomery conversion.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

structure Montgomery (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region) where
  op : Nat → Nat → Nat → Prog isa
  workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions
  stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
    Rest roundClobbers s t → P s → P t
  op_ok : ∀ (s : State) (o a b : Nat), ArithmeticReady base len w s → P s →
    Operand o → Operand a → Operand b → o ≠ 0 →
    numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0 →
    WP isa (op o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b %
          numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t

end VG.Proof.Bignum.Arm.TwoExp
