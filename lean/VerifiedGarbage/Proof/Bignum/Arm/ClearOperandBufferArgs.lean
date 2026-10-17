module

public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Derive the public width and address of an extended operand buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_lsl op2_imm dpVal)

theorem clearOperandBufferArgs_ok (s : State) {base dst : BitVec 32} {size slot w : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096)
    (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (link : s.mem.readW (off (State.addr base) slot) 32 = dst) :
    WP isa (.block (clearOperandBufferArgs slot)) s fun t => t.gpr .r0 = dst ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w + 2) ∧ t.gpr .r3 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r3, .lr] s t := by
  unfold clearOperandBufferArgs
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u a => ?_
  refine wp_mov (op2_lsl (by decide)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun z c => ?_
  refine wp_mov (op2_imm (by decide)) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) slot) hs
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide), ptr]
        exact addr_add (by have := ws.nowrap; omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact ws.read slotFit) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, (e.other .r3 (by decide)).trans d.gpr,
    e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans (e.rest (by simp)))))⟩
  · rw [e.gpr, d.mem, c.mem, b.mem, a.mem]; exact link
  · rw [e.other .lr (by decide), d.other .lr (by decide), c.gpr, dpVal, b.gpr, a.gpr, count,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 w * BitVec.ofNat 32 2 + BitVec.ofNat 32 2 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm w 2]

end VG.Proof.Bignum.Arm
