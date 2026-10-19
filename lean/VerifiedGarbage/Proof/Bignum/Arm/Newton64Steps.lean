module

public import VerifiedGarbage.Impl.Bignum.Arm.Newton64
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Sub64
import VerifiedGarbage.Proof.Framework.Block

/-! # Loading, subtracting, and retaining one Newton iterate -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_reg op2_imm)

theorem newton64Load_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4) :
    WP isa (.block newton64Load) s fun t =>
      (t.gpr .r11 ++ t.gpr .r2) = (s.mem.readW b 32 ++ s.mem.readW a 32) ∧
      t.mem = s.mem ∧ Rest [.r2, .r11] s t := by
  unfold newton64Load
  refine wp_ldr (a := a) (by decide) pa ra fun s1 u1 => ?_
  refine wp_ldr (a := b) (by decide) (by rw [u1.other .r0 (by decide)]; exact pb)
    (by rw [u1.rd, u1.wr]; exact rb) fun t u2 => WP.block_nil ?_
  refine ⟨?_, u2.mem.trans u1.mem, (u1.rest (by simp)).trans (u2.rest (by simp))⟩
  rw [u2.gpr, u2.other .r2 (by decide), u1.gpr, u1.mem]

theorem newton64Subtract_ok (s : State) :
    WP isa (.block newton64Subtract) s fun t =>
      (t.gpr .r11 ++ t.gpr .r2) = (2 : BitVec 64) - (s.gpr .r4 ++ s.gpr .r3) ∧
      t.mem = s.mem ∧ Rest [.r2, .r5, .r6, .r11] s t := by
  rw [newton64Subtract, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u h => WP.block_nil ?_
  refine WP.mono (sub64_ok u) ?_
  rintro t ⟨val, mem, rest⟩
  refine ⟨?_, mem.trans h.mem, (h.rest (by simp)).trans (rest.mono (by simp))⟩
  rw [val, h.gpr, h.other .r3 (by decide), h.other .r4 (by decide)]
  rfl

theorem newton64Finish_ok (s : State) :
    WP isa (.block newton64Finish) s fun t =>
      (t.gpr .r10 ++ t.gpr .r1) = (s.gpr .r4 ++ s.gpr .r3) ∧
      t.mem = s.mem ∧ Rest [.r1, .r10] s t := by
  unfold newton64Finish
  refine wp_mov (op2_reg _ _) fun u h => ?_
  refine wp_mov (op2_reg _ _) fun t j => WP.block_nil ?_
  refine ⟨?_, j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩
  rw [j.gpr, j.other .r1 (by decide), h.gpr, h.other .r4 (by decide)]

end VG.Proof.Bignum.Arm
