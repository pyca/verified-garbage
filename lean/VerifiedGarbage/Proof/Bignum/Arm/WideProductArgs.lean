module

public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Load the fixed-schedule wide-product row arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm)

theorem wideProductArgs_ok (s : State) {base : BitVec 32} {size a b o n : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (aFit : a + 4 ≤ size)
    (ptr : s.gpr .r0 = base)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = base + BitVec.ofNat 32 a)
    (bPtr : s.mem.readW (off (State.addr base) 132) 32 = base + BitVec.ofNat 32 b)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = base + BitVec.ofNat 32 o)
    (count : s.mem.readW (off (State.addr base) 144) 32 = BitVec.ofNat 32 n) :
    WP isa (.block wideProductArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 o ∧ t.gpr .r12 = base + BitVec.ofNat 32 b ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r1 = s.mem.readW (off (State.addr base) a) 32 ∧
      t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r11, .r12, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold wideProductArgs wideProductArgsHead wideProductArgsTail
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (a := off (State.addr base) 132) (by decide) (addr 132 (by omega))
    (ws.read (by omega)) fun u h => ?_
  refine wp_ldr (a := off (State.addr base) 144) (by decide)
    (by rw [h.other .r0 (by decide)]; exact addr 144 (by omega))
    (by rw [h.rd, h.wr]; exact ws.read (by omega)) fun v j => ?_
  refine wp_ldr (a := off (State.addr base) 128) (by decide)
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact addr 128 (by omega))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact ws.read (by omega)) fun z l => ?_
  refine wp_ldr (a := off (State.addr base) a) (by decide)
    (by rw [l.gpr, j.mem, h.mem, aPtr, BitVec.add_zero]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [l.rd, l.wr, j.rd, j.wr, h.rd, h.wr]; exact ws.read aFit) fun q c => ?_
  refine wp_mov (op2_imm (by decide)) fun p d => ?_
  refine wp_ldr (a := off (State.addr base) 136) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), l.other .r0 (by decide),
      j.other .r0 (by decide), h.other .r0 (by decide)]; exact addr 136 (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, l.rd, l.wr, j.rd, j.wr, h.rd, h.wr]; exact ws.read (by omega)) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (l.mem.trans (j.mem.trans h.mem)))),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans ((l.rest (by simp)).trans
      ((c.rest (by simp)).trans ((d.rest (by simp)).trans (e.rest (by simp))))))⟩
  · rw [e.gpr, d.mem, c.mem, l.mem, j.mem, h.mem]; exact oPtr
  · rw [e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide),
      l.other .r12 (by decide), j.other .r12 (by decide), h.gpr]; exact bPtr
  · rw [e.other .lr (by decide), d.other .lr (by decide), c.other .lr (by decide),
      l.other .lr (by decide), j.gpr, h.mem]; exact count
  · rw [e.other .r1 (by decide), d.other .r1 (by decide), c.gpr, l.mem, j.mem, h.mem]
  · rw [e.other .r11 (by decide), d.gpr]

end VG.Proof.Bignum.Arm
