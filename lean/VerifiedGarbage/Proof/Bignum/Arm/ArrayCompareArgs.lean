module

public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Native pointers for the constant-time RSA input range check -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_reg op2_imm dpVal)

theorem arrayCompareArgs_ok (s : State) {base : BitVec 32} {size w lhs rhs : Nat}
    {arr : Nat → Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 128 ≤ size)
    (ha : lhs < 8) (hb : rhs < 8)
    (header : NativeHeader s.mem base w arr inv) (ptr : s.gpr .r0 = base) :
    WP isa (.block (arrayCompareArgs lhs rhs)) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arr 3) ∧
      t.gpr .r10 = base + BitVec.ofNat 32 (arr lhs) ∧
      t.gpr .r12 = base + BitVec.ofNat 32 (arr rhs) ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧ t.gpr .r11 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r10, .r11, .r12, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold arrayCompareArgs
  refine wp_ldr (a := off (State.addr base) (64 + 8 * lhs)) (by omega) (addr (64 + 8 * lhs) (by omega))
    (ws.read (by omega)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) (64 + 8 * rhs)) (by omega)
    (by rw [a.other .r0 (by decide)]; exact addr (64 + 8 * rhs) (by omega))
    (by rw [a.rd, a.wr]; exact ws.read (by omega)) fun v b => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact ws.read (by omega)) fun z c => ?_
  refine wp_dp (op2_reg _ _) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) 88) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 88 (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact ws.read (by omega)) fun p e => ?_
  refine wp_mov (op2_imm (by decide)) fun t f => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, f.gpr, f.mem.trans (e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem)))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans ((e.rest (by simp)).trans (f.rest (by simp))))))⟩
  · rw [f.other .r0 (by decide), e.gpr, d.mem, c.mem, b.mem, a.mem]
    exact header.array 3 (by decide)
  · rw [f.other .r10 (by decide), e.other .r10 (by decide), d.other .r10 (by decide),
      c.other .r10 (by decide), b.other .r10 (by decide), a.gpr]
    exact header.array lhs ha
  · rw [f.other .r12 (by decide), e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide), b.gpr, a.mem]
    exact header.array rhs hb
  · rw [f.other .lr (by decide), e.other .lr (by decide), d.gpr, dpVal, c.gpr, b.mem, a.mem, header.count,
      ← BitVec.ofNat_add, show w + w = 2 * w by omega]

end VG.Proof.Bignum.Arm
