module

public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Native pointers for branchless array selection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_reg op2_imm dpVal)

theorem selectArrayArgs_ok (s : State) {base : BitVec 32} {size w o a b : Nat}
    {arr : Nat → Nat} {inv : BitVec 32}
    (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ws : Workspace s base size) (fit : 128 ≤ size)
    (header : NativeHeader s.mem base w arr inv) (ptr : s.gpr .r0 = base) :
    WP isa (.block (selectArrayArgs o a b)) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arr o) ∧
      t.gpr .r10 = base + BitVec.ofNat 32 (arr a) ∧
      t.gpr .r12 = base + BitVec.ofNat 32 (arr b) ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧
      t.mem = s.mem ∧ Rest [.r0, .r10, .r12, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold selectArrayArgs
  refine wp_ldr (a := off (State.addr base) (64 + 8 * a)) (by omega) (addr (64 + 8 * a) (by omega))
    (ws.read (by omega)) fun u loadA => ?_
  refine wp_ldr (a := off (State.addr base) (64 + 8 * b)) (by omega)
    (by rw [loadA.other .r0 (by decide)]; exact addr (64 + 8 * b) (by omega))
    (by rw [loadA.rd, loadA.wr]; exact ws.read (by omega)) fun v loadB => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by omega)
    (by rw [loadB.other .r0 (by decide), loadA.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [loadB.rd, loadB.wr, loadA.rd, loadA.wr]; exact ws.read (by omega)) fun z c => ?_
  refine wp_dp (op2_reg _ _) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) (64 + 8 * o)) (by omega)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), loadB.other .r0 (by decide), loadA.other .r0 (by decide)]; exact addr (64 + 8 * o) (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, loadB.rd, loadB.wr, loadA.rd, loadA.wr]; exact ws.read (by omega)) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (loadB.mem.trans loadA.mem))),
    (loadA.rest (by simp)).trans ((loadB.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans (e.rest (by simp)))))⟩
  · rw [e.gpr, d.mem, c.mem, loadB.mem, loadA.mem]
    exact header.array o ho
  · rw [e.other .r10 (by decide), d.other .r10 (by decide),
      c.other .r10 (by decide), loadB.other .r10 (by decide), loadA.gpr]
    exact header.array a ha
  · rw [e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide), loadB.gpr, loadA.mem]
    exact header.array b hb
  · rw [e.other .lr (by decide), d.gpr, dpVal, c.gpr, loadB.mem, loadA.mem, header.count,
      ← BitVec.ofNat_add, show w + w = 2 * w by omega]

end VG.Proof.Bignum.Arm
