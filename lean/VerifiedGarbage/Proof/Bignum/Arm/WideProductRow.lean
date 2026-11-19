module

public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
import VerifiedGarbage.Proof.Bignum.Arm.ProductRowMath
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! ### `Bignum.Arm.WideProductState`, which this module and modules that import it used -/

section

/-! # Invariants for an exact wide product with fixed public row counts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure WideProductCtx (s : State) (base : BitVec 32) (size o a b m n : Nat) : Prop where
  workspace : Workspace s base size
  positiveA : 0 < m
  positiveB : 0 < n
  headerFit : 148 ≤ size
  aHeader : 256 ≤ a
  bHeader : 256 ≤ b
  oHeader : 256 ≤ o
  aFits : a + 4 * m ≤ size
  bFits : b + 4 * n ≤ size
  outFits : o + 4 * (m + n + 2) ≤ size
  separateA : o + 4 * (m + n + 2) ≤ a ∨ a + 4 * m ≤ o
  separateB : o + 4 * (m + n + 2) ≤ b ∨ b + 4 * n ≤ o
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

structure WideProductInv (s0 : State) (base : BitVec 32) (o a b m n i : Nat) (s : State) : Prop where
  index : i ≤ m
  ptr : s.gpr .r0 = base
  aPtr : s.mem.readW (off (State.addr base) 128) 32 = base + BitVec.ofNat 32 (a + 4 * i)
  bPtr : s.mem.readW (off (State.addr base) 132) 32 = base + BitVec.ofNat 32 b
  oPtr : s.mem.readW (off (State.addr base) 136) 32 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 (m - i)
  width : s.mem.readW (off (State.addr base) 144) 32 = BitVec.ofNat 32 n
  outside : Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s0.mem s.mem
  value : val32 s.mem (State.addr base) o (m + n + 2) =
    val32 s0.mem (State.addr base) a i * val32 s0.mem (State.addr base) b n
  rest : Rest roundClobbers s0 s

theorem WideProductCtx.frame {s t : State} {base : BitVec 32} {size o a b m n : Nat}
    (h : WideProductCtx s base size o a b m n)
    (outside : Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem t.mem) :
    Frame [⟨State.addr base, size⟩] s.mem t.mem := by
  refine outside_workspace (o := 0) (n := size) ?_ (by omega_using [])
  intro x hx
  apply outside x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have := h.headerFit
  have := h.outFits
  rcases hr with rfl | rfl <;> omega_arith

theorem WideProductInv.source {s0 s : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx : WideProductCtx s0 base size o a b m n) (h : WideProductInv s0 base o a b m n i s) (hi : i < m) :
    w32 s.mem (State.addr base) (a + 4 * i) = w32 s0.mem (State.addr base) (a + 4 * i) ∧
      val32 s.mem (State.addr base) b n = val32 s0.mem (State.addr base) b n := by
  have nowrap := ctx.workspace.nowrap
  have aFits := ctx.aFits
  have bFits := ctx.bFits
  have aHeader := ctx.aHeader
  have bHeader := ctx.bHeader
  have sepA := ctx.separateA
  have sepB := ctx.separateB
  have word := h.outside.val32 (d := a + 4 * i) (k := 1)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> omega_arith) (by omega_using [hi, nowrap, aFits])
  refine ⟨?_, h.outside.val32 ?_ (by omega_using [nowrap, bFits])⟩
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using word
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega_arith

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.WideProductArgs`, which this module and modules that import it used -/

section

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
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega_using [hd, this])
  unfold wideProductArgs wideProductArgsHead wideProductArgsTail
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (a := off (State.addr base) 132) (by decide) (addr 132 (by omega_using [fit]))
    (ws.read (by omega_using [fit])) fun u h => ?_
  refine wp_ldr (a := off (State.addr base) 144) (by decide)
    (by rw [h.other .r0 (by decide)]; exact addr 144 (by omega_using [fit]))
    (by rw [h.rd, h.wr]; exact ws.read (by omega_using [fit])) fun v j => ?_
  refine wp_ldr (a := off (State.addr base) 128) (by decide)
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact addr 128 (by omega_using [fit]))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact ws.read (by omega_using [fit])) fun z l => ?_
  refine wp_ldr (a := off (State.addr base) a) (by decide)
    (by rw [l.gpr, j.mem, h.mem, aPtr, BitVec.add_zero]; exact addr_add (by have := ws.nowrap; omega_using [aFit, this]))
    (by rw [l.rd, l.wr, j.rd, j.wr, h.rd, h.wr]; exact ws.read aFit) fun q c => ?_
  refine wp_mov (op2_imm (by decide)) fun p d => ?_
  refine wp_ldr (a := off (State.addr base) 136) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), l.other .r0 (by decide),
      j.other .r0 (by decide), h.other .r0 (by decide)]; exact addr 136 (by omega_using [fit]))
    (by rw [d.rd, d.wr, c.rd, c.wr, l.rd, l.wr, j.rd, j.wr, h.rd, h.wr]; exact ws.read (by omega_using [fit])) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (l.mem.trans (j.mem.trans h.mem)))),
    (h.rest (by decide)).trans ((j.rest (by decide)).trans ((l.rest (by decide)).trans
      ((c.rest (by decide)).trans ((d.rest (by decide)).trans (e.rest (by decide))))))⟩
  · rw [e.gpr, d.mem, c.mem, l.mem, j.mem, h.mem]; exact oPtr
  · rw [e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide),
      l.other .r12 (by decide), j.other .r12 (by decide), h.gpr]; exact bPtr
  · rw [e.other .lr (by decide), d.other .lr (by decide), c.other .lr (by decide),
      l.other .lr (by decide), j.gpr, h.mem]; exact count
  · rw [e.other .r1 (by decide), d.other .r1 (by decide), c.gpr, l.mem, j.mem, h.mem]
  · rw [e.other .r11 (by decide), d.gpr]

end VG.Proof.Bignum.Arm

end

end

/-! # One complete product row implements the next schoolbook multiplication term -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductRow_ok (s : State) {s0 : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx : WideProductCtx s0 base size o a b m n) (h : WideProductInv s0 base o a b m n i s) (hi : i < m) :
    WP isa (.seq (.block wideProductArgs) (.seq rowFull (.block [.ldrSp .r0 0]))) s fun t =>
      val32 t.mem (State.addr base) o (m + n + 2) =
        val32 s0.mem (State.addr base) a (i + 1) * val32 s0.mem (State.addr base) b n ∧
      Outside (State.addr base) (o + 4 * i) (4 * (n + 2)) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have aFits := ctx.aFits
  have bFits := ctx.bFits
  have outFits := ctx.outFits
  have sepB := ctx.separateB
  obtain ⟨aOld, bOld⟩ := h.source ctx hi
  have window := product_window_bound (by omega_using [hi] : i + (n + 2) ≤ m + n + 2) h.value
    (val32_lt s0.mem (State.addr base) a i) (val32_lt s0.mem (State.addr base) b n)
  rw [WP.seq_iff]
  refine WP.mono (wideProductArgs_ok s (ctx.workspace.congr h.rest.wr) ctx.headerFit (by omega_using [hi, aFits])
    h.ptr h.aPtr h.bPtr h.oPtr h.width) ?_
  rintro u ⟨p0, p12, count, scalar, zero, memU, restU⟩
  have rowCtx : RowCtx u base size (o + 4 * i) b n :=
    ⟨nowrap, by omega_using [hi, outFits], bFits, by omega_using [hi, sepB], by rw [restU.wr, h.rest.wr]; exact ctx.workspace.writable⟩
  have fit : val32 u.mem (State.addr base) (o + 4 * i) (n + 2) +
      (u.gpr .r1).toNat * val32 u.mem (State.addr base) b n + (u.gpr .r11).toNat < 2 ^ (32 * (n + 2)) := by
    rw [zero, scalar, memU]
    exact product_row_fits window (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
      (val32_lt s.mem (State.addr base) b n)
  rw [WP.seq_iff]
  refine WP.mono (rowFull_ok u rowCtx ctx.positiveB (by omega_using [hi, outFits]) p0 p12 count fit) ?_
  rintro v ⟨value, outside, _, restV⟩
  rw [memU] at outside
  rw [zero, scalar, memU] at value
  change val32 v.mem (State.addr base) (o + 4 * i) (n + 2) =
    val32 s.mem (State.addr base) (o + 4 * i) (n + 2) +
      w32 s.mem (State.addr base) (a + 4 * i) * val32 s.mem (State.addr base) b n at value
  rw [aOld, bOld] at value
  have whole := product_row_value (by omega_using [hi] : i + (n + 2) ≤ m + n + 2) (by omega_using [nowrap, outFits]) outside h.value value
  have frame := outside_workspace outside (size := size) (by omega_using [hi, outFits])
  have restSV : Rest roundClobbers s v := (restU.mono (by decide)).trans
    (restV.mono (by decide))
  have rest := h.rest.trans restSV
  have frameAll := (ctx.frame h.outside).trans frame
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact ctx.stackRead)
    (saved_base_kept frameAll ctx.stackSep ctx.saved rest.sp)) ?_
  rintro t ⟨ptr, memT, restT⟩
  exact ⟨by rw [memT]; exact whole, by rw [memT]; exact outside, ptr,
    restSV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
