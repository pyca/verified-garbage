module

public import VerifiedGarbage.Impl.Bignum.Arm.MaskOutput
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Form an all-zero or all-one mask without branching on acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem maskOutputArgs_ok (s : State)
    (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4) :
    WP isa (.block maskOutputArgs) s fun t =>
      t.gpr .r0 = s.gpr .r4 ∧ t.gpr .lr = s.gpr .r6 ∧
      t.gpr .r4 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      t.gpr .r2 = -s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      t.mem = s.mem ∧ Rest [.r0, .r2, .r4, .lr] s t := by
  unfold maskOutputArgs
  refine wp_mov (op2_reg _ _) fun u a => ?_
  refine wp_mov (op2_reg _ _) fun v b => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 48) (by decide)
    (by rw [b.sp, a.sp]; exact addr_add (by omega)) (by rw [b.rd, b.wr, a.rd, a.wr]; exact read) fun z c => ?_
  refine wp_mov (op2_imm (by decide)) fun q d => ?_
  refine wp_dp (op2_reg _ _) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans (e.rest (by simp)))))⟩
  · rw [e.other .r0 (by decide), d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.gpr]
  · rw [e.other .lr (by decide), d.other .lr (by decide), c.other .lr (by decide), b.gpr, a.other .r6 (by decide)]
  · rw [e.other .r4 (by decide), d.other .r4 (by decide), c.gpr, b.mem, a.mem]
  · rw [e.gpr, dpVal, d.gpr, d.other .r4 (by decide), c.gpr, b.mem, a.mem]
    exact BitVec.zero_sub _

end VG.Proof.Bignum.Arm
