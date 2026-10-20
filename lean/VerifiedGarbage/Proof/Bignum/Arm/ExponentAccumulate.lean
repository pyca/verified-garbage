module

public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # Read the next public exponent byte into a pair of native words -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_mov wp_dp wp_subs op2_lsr op2_lsl op2_reg op2_imm dpVal)

theorem exponentAccumulate_ok (s : State) {p : Addr}
    (ptr : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = p)
    (read : InRegions (s.rd ++ s.wr) p 1) :
    WP isa (.block exponentAccumulate) s fun t =>
      t.gpr .r3 = (s.gpr .r3 <<< 8) + (s.mem p).setWidth 32 ∧
      t.gpr .r4 = (s.gpr .r4 <<< 8) + (s.gpr .r3 >>> 24) ∧
      t.z = ((((s.gpr .r4 <<< 8) + (s.gpr .r3 >>> 24)) >>> 1) == 0) ∧
      t.mem = s.mem ∧ Rest [.r3, .r4, .r5, .r7] s t := by
  unfold exponentAccumulate
  refine wp_ldrb (by decide) ptr read fun s1 a => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 b => ?_
  refine wp_mov (op2_lsl (by decide)) fun s3 c => ?_
  refine wp_dp (op2_reg _ _) fun s4 d => ?_
  refine wp_mov (op2_lsl (by decide)) fun s5 e => ?_
  refine wp_dp (op2_reg _ _) fun s6 f => ?_
  refine wp_mov (op2_lsr (by decide)) fun s7 g => ?_
  refine wp_subs (op2_imm (by decide)) fun t h zero => WP.block_nil ?_
  have high : s4.gpr .r4 = (s.gpr .r4 <<< 8) + (s.gpr .r3 >>> 24) := by
    rw [d.gpr, dpVal, c.gpr, b.other .r4 (by decide), a.other .r4 (by decide),
      c.other .r5 (by decide), b.gpr, a.other .r3 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.other .r3 (by decide), g.other .r3 (by decide), f.gpr, dpVal, e.gpr,
      d.other .r3 (by decide), c.other .r3 (by decide), b.other .r3 (by decide), a.other .r3 (by decide),
      e.other .r7 (by decide), d.other .r7 (by decide), c.other .r7 (by decide), b.other .r7 (by decide), a.gpr]
  · rw [h.other .r4 (by decide), g.other .r4 (by decide), f.other .r4 (by decide), e.other .r4 (by decide), high]
  · have subzero : s7.gpr .r5 - (0 : BitVec 32) = s7.gpr .r5 := BitVec.sub_zero _
    rw [zero, subzero, g.gpr, f.other .r4 (by decide), e.other .r4 (by decide), high]
  · rw [h.mem, g.mem, f.mem, e.mem, d.mem, c.mem, b.mem, a.mem]
  · exact (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans ((e.rest (by simp)).trans ((f.rest (by simp)).trans
      ((g.rest (by simp)).trans (h.rest (by simp))))))))

end VG.Proof.Bignum.Arm
