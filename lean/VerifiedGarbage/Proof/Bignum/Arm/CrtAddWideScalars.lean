module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtAddWide
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Set an extended addition's scalar and carry to one and zero -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm dpVal)

theorem crt_addWideScalars_ok (s : State) {w : Nat} (count : s.gpr .lr = BitVec.ofNat 32 (4 * w + 2)) :
    WP isa (.block addWideScalars) s fun t => t.gpr .lr = BitVec.ofNat 32 (4 * w) ∧
      t.gpr .r1 = 1 ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r1, .r11, .lr] s t := by
  unfold addWideScalars
  refine wp_dp (op2_imm (by decide)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun v b => ?_
  refine wp_mov (op2_imm (by decide)) fun t c => WP.block_nil ?_
  refine ⟨?_, (c.other .r1 (by decide)).trans b.gpr, c.gpr, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩
  rw [c.other .lr (by decide), b.other .lr (by decide), a.gpr, dpVal, count, BitVec.ofNat_add]
  change (BitVec.ofNat 32 (4 * w) + 2#32) - 2#32 = _
  exact BitVec.add_sub_cancel _ _

end VG.Proof.Bignum.Arm
