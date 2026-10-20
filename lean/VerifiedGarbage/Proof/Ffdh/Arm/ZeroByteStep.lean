module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.TCB.Arm.Isa

/-! One zeroed scalar-prefix byte, optionally advancing the entropy pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest wp_strb wp_dp wp_subs op2_imm dpVal)

theorem zeroByteStep_ok (advance : Bool) (s : State) (dst : Addr)
    (pd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = dst) (write : InRegions s.wr dst 1)
    (zero : s.gpr .r2 = 0) :
    WP isa (.block (if advance then VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep
      else VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep)) s fun t =>
      t.mem = s.mem.writeW dst (0#8) ∧ t.gpr .r0 = s.gpr .r0 + 1 ∧
      t.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 advance.toNat ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r1, .lr] s t := by
  cases advance
  · change WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep) s _
    unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep
    refine wp_strb (by decide) pd write fun u stored => ?_
    refine wp_dp (op2_imm (by decide)) fun v moved => ?_
    refine wp_subs (op2_imm (by decide)) fun t counted z => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [counted.mem, moved.mem, stored.mem, zero]; rfl
    · rw [counted.other .r0 (by decide), moved.gpr, dpVal, stored.gpr]
    · rw [counted.other .r1 (by decide), moved.other .r1 (by decide), stored.gpr]
      simp
    · rw [counted.gpr, moved.other .lr (by decide), stored.gpr]
    · rw [z, moved.other .lr (by decide), stored.gpr]
    · exact (stored.rest _).trans ((moved.rest (by simp)).trans (counted.rest (by simp)))
  · change WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) s _
    unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep
    refine wp_strb (by decide) pd write fun u stored => ?_
    refine wp_dp (op2_imm (by decide)) fun v moved => ?_
    refine wp_dp (op2_imm (by decide)) fun w source => ?_
    refine wp_subs (op2_imm (by decide)) fun t counted z => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [counted.mem, source.mem, moved.mem, stored.mem, zero]; rfl
    · rw [counted.other .r0 (by decide), source.other .r0 (by decide), moved.gpr, dpVal, stored.gpr]
    · rw [counted.other .r1 (by decide), source.gpr, dpVal, moved.other .r1 (by decide), stored.gpr]; rfl
    · rw [counted.gpr, source.other .lr (by decide), moved.other .lr (by decide), stored.gpr]
    · rw [z, source.other .lr (by decide), moved.other .lr (by decide), stored.gpr]
    · exact (stored.rest _).trans ((moved.rest (by simp)).trans ((source.rest (by simp)).trans (counted.rest (by simp))))

end VG.Proof.Ffdh.Arm
