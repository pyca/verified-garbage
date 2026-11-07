module

public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpState
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # A generic generator-two bit step

Arithmetic actions may write an additional callee-stack region. Their
persistent predicate records those calling conditions; the exponent loop
only assumes the stated power, header, frame, and register guarantees.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_lsr op2_imm dpVal)

abbrev HeaderKept (base : BitVec 32) (s t : State) : Prop :=
  ∀ d, d + 4 ≤ 256 → t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32

structure Kernel (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region) where
  square : Prog isa
  twice : Prog isa
  workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions
  stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
    Rest roundClobbers s t → P s → P t
  square_ok : ∀ (s : State) (E : Nat) {M : Nat}, Power base len w M E s → P s →
    WP isa square s fun t => Power base len w M (2 * E) t ∧ P t ∧ HeaderKept base s t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  twice_ok : ∀ (s : State) (E : Nat) {M : Nat}, Power base len w M E s → P s →
    WP isa twice s fun t => Power base len w M E t ∧
      numAt t.mem (State.addr base) w 1 < M ∧
      numAt t.mem (State.addr base) w 1 % M = 2 ^ (E + 1) * 2 ^ (64 * w) % M ∧
      P t ∧ HeaderKept base s t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t

end VG.Proof.Bignum.Arm.TwoExp
