module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.Bignum.Arm.StackPair
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public stack-relative arguments for the masked release loop -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem releaseArgs_ok (s : State) (fit : s.sp.toNat + 76 ≤ 2 ^ 32)
    (outRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) oOut) 4)
    (countRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) oK) 4) :
    WP isa (.block releaseArgs) s fun t =>
      t.gpr .r0 = s.mem.readW (off (State.addr s.sp) oOut) 32 ∧
      t.gpr .r1 = s.sp + BitVec.ofNat 32 oM ∧
      t.gpr .lr = s.mem.readW (off (State.addr s.sp) oK) 32 ∧ t.gpr .r12 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r12, .lr] s t := by
  unfold releaseArgs
  refine wp_loadStack (a := off (State.addr s.sp) oOut) (by decide)
    (addr_add (by simp only [oOut]; omega)) outRead fun u a => ?_
  refine wp_stackAddr (by decide) fun v b => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oK) (by decide)
    (by rw [b.sp, a.sp]; exact addr_add (by simp only [oK]; omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact countRead) fun z c => ?_
  refine wp_mov (op2_imm (by decide)) fun t d => WP.block_nil ?_
  exact ⟨by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.gpr],
    by rw [d.other .r1 (by decide), c.other .r1 (by decide), b.gpr, a.sp],
    by rw [d.other .lr (by decide), c.gpr, b.mem, a.mem], d.gpr,
    d.mem.trans (c.mem.trans (b.mem.trans a.mem)),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans (d.rest (by simp))))⟩
end VG.Proof.Rsa.Arm
