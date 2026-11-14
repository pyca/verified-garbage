module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! ### `Bignum.Arm.TwoExpKernel`, which only this module used -/

section

/-! # The header kept by the generator-two exponent loop

`header_of_keeps`: an action that keeps the arithmetic layout keeps the
header (`HeaderKept`).
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem header_of_keeps {base : BitVec 32} {len w o : Nat} {s t : State}
    (ready : ArithmeticReady base len w s) (keeps : Keeps (State.addr base) len w o s.mem t.mem) :
    HeaderKept base s t := by
  have fit : arrAt w 8 ≤ 8 * len := ready.width ▸ ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega_using [fit]
  intro d hd
  exact keeps_header_readW keeps size (d := d) (bits := 32) (by omega_using [hd])

end VG.Proof.Bignum.Arm.TwoExp

end

end


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
