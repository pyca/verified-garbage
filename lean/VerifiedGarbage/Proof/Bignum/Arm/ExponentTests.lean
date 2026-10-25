module

public import VerifiedGarbage.Proof.Bignum.ExponentTestMath
public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Word tests for public-exponent limits, parity, and rejection of one -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp wp_subs op2_lsr op2_imm op2_reg dpVal)

theorem exponentBoundsTest_ok (s : State) :
    WP isa (.block exponentBoundsTest) s fun t =>
      t.z = exponentBounds (s.gpr .r3) (s.gpr .r4) ∧
      t.mem = s.mem ∧ Rest [.r5, .r7] s t := by
  unfold exponentBoundsTest
  refine wp_mov (op2_lsr (by decide)) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun q c => ?_
  refine wp_dp (op2_reg _ _) fun r d => ?_
  refine wp_subs (op2_imm (by decide)) fun t e zero => WP.block_nil ?_
  refine ⟨?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans (e.rest (by decide)))))⟩
  have subzero : r.gpr .r5 - (0 : BitVec 32) = r.gpr .r5 := BitVec.sub_zero _
  rw [zero, subzero, d.gpr, dpVal, c.other .r5 (by decide), b.other .r5 (by decide), a.gpr,
    c.gpr, dpVal, b.gpr, dpVal, a.other .r3 (by decide)]
  rfl

theorem exponentOneTest_ok (s : State) :
    WP isa (.block exponentOneTest) s fun t =>
      t.z = exponentIsOne (s.gpr .r3) (s.gpr .r4) ∧
      t.mem = s.mem ∧ Rest [.r5, .r7] s t := by
  unfold exponentOneTest
  refine wp_dp (op2_imm (by decide)) fun u a => ?_
  refine wp_dp (op2_reg _ _) fun v b => ?_
  refine wp_subs (op2_imm (by decide)) fun t c zero => WP.block_nil ?_
  refine ⟨?_, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))⟩
  have subzero : v.gpr .r5 - (0 : BitVec 32) = v.gpr .r5 := BitVec.sub_zero _
  rw [zero, subzero, b.gpr, dpVal, a.gpr, dpVal, a.other .r4 (by decide)]
  rfl

theorem exponentResult_ok (s : State) (b : Bool) :
    WP isa (exponentResult b) s fun t => t.gpr .r7 = BitVec.ofNat 32 b.toNat ∧
      t.mem = s.mem ∧ Rest [.r5, .r7] s t := by
  unfold exponentResult
  refine wp_mov (op2_imm (by cases b <;> decide)) fun t h => WP.block_nil ?_
  exact ⟨h.gpr, h.mem, h.rest (by decide)⟩

end VG.Proof.Bignum.Arm
