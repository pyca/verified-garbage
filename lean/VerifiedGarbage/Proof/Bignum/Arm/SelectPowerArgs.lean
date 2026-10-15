module

public import VerifiedGarbage.Impl.Bignum.Arm.SelectPower
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Native pointers for branchless private-power selection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_reg op2_imm dpVal)

theorem selectPowerArgs_ok (s : State) {base : BitVec 32} {size w : Nat}
    {arr : Nat → Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 128 ≤ size)
    (header : NativeHeader s.mem base w arr inv) (ptr : s.gpr .r0 = base) :
    WP isa (.block selectPowerArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arr 6) ∧
      t.gpr .r10 = base + BitVec.ofNat 32 (arr 6) ∧
      t.gpr .r12 = base + BitVec.ofNat 32 (arr 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧
      t.mem = s.mem ∧ Rest [.r0, .r10, .r12, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold selectPowerArgs
  refine wp_ldr (a := off (State.addr base) 112) (by decide) (addr 112 (by omega))
    (ws.read (by omega)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 72) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 72 (by omega))
    (by rw [a.rd, a.wr]; exact ws.read (by omega)) fun v b => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact ws.read (by omega)) fun z c => ?_
  refine wp_dp (op2_reg _ _) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) 112) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 112 (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact ws.read (by omega)) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans (e.rest (by simp)))))⟩
  · rw [e.gpr, d.mem, c.mem, b.mem, a.mem]
    exact header.array 6 (by decide)
  · rw [e.other .r10 (by decide), d.other .r10 (by decide),
      c.other .r10 (by decide), b.other .r10 (by decide), a.gpr]
    exact header.array 6 (by decide)
  · rw [e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide), b.gpr, a.mem]
    exact header.array 1 (by decide)
  · rw [e.other .lr (by decide), d.gpr, dpVal, c.gpr, b.mem, a.mem, header.count,
      ← BitVec.ofNat_add, show w + w = 2 * w by omega]

end VG.Proof.Bignum.Arm
