module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
public import VerifiedGarbage.Proof.Ed25519.Point64Contract
public import VerifiedGarbage.Proof.Ed25519.AArch64.Points
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ed25519.AArch64.Field
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
public import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ed25519.CombDigits

/-! ### `Ed25519.AArch64.CombLoop`, which this module and modules that import it used -/

section

/-! ### `Ed25519.AArch64.CombStart`, which this module and modules that import it used -/

section

/-!
# Where the AArch64 comb starts: `combStart` represents `[17 G]B`

For the comb's offset `G = combGVal`: the kernel compares `combStart` with `pointMul` of the
base point (`combStart_ok`, as `combG_ok`), and `combStart8` with `[17 G - 8]B`, where the comb
of a scalar with bits 0–2 clear starts for bit 3 clear (`combStart8_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG.Spec.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

private def combStartCheck (p : Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check : combStartCheck (pointMul (17 * combGVal) basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * combGVal) • baseAff) := by
  have hp := pointMul_rep (17 * combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStartAff) hp hx hy

private def combStart8Check (p : Point) : Bool :=
  combStart8.X * p.Z == p.X && combStart8.Y * p.Z == p.Y && p.Z != 0

private theorem combStart8_check :
    combStart8Check (pointMul (17 * combGVal - 8) basePoint) = true := by
  decide +kernel

theorem combStart8_ok : Rep combStart8 ((17 * combGVal - 8) • baseAff) := by
  have hp := pointMul_rep (17 * combGVal - 8) basePoint_rep
  have hc := combStart8_check
  simp only [combStart8Check, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStart8Aff) hp hx hy

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.CombAdd`, which only this module used -/

section

/-! ### `Ed25519.AArch64.Point64.Fn`, which only this module used -/

section

/-!
# Ed25519's point functions on AArch64: the affine addition's value

Untrusted: everything here is checked by Lean. The affine addition's program
computes `pointAdd` of an entry with `Z = 1` (`mixedResult_eq`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Point64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

/-! ## The programs' values -/

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

end VG.Proof.Ed25519.AArch64.Point64

end

end


/-!
# The comb's addition, on the `_alt` operations

`combAdd` adds the affine entry in slots 4–6 to the accumulator in slots 0–3
with `addAffineOps`' formula (`mixedResult`), on the operations of `AltOps`
(`combAdd_ok`). Its sums and differences need inputs below `2·p`, which the
accumulator's coordinates are, as products of `mul_4`, between additions
(`AccBel`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.X25519.AArch64.Alt (AltOp)
open VG.Proof.X25519.AArch64.AltLadder (P2 mulE addE addE1 subE fr x17_ok altClob_sub)

variable {large : Bool}

/-- The accumulator's coordinates (slots 0–3) are below `2·p`. -/
def AccBel (m : Mem) (base : Addr) : Prop := ∀ i : Slot, i.val < 4 → fe m base (offset i) < P2

theorem _root_.VG.Proof.X25519.AArch64.Alt.AltOp.keep {base : Addr} {o : Slot} {s t : State} (h : AltOp base (offset o) s t)
    (ho : o.val ≤ 13) : Keep base s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (altClob_sub r hm)), h.rd, h.wr, h.sp,
    h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega_using [])⟩

theorem _root_.VG.Proof.X25519.AArch64.Alt.AltOp.x17 {base : Addr} {o : Nat} {s t : State} (h : AltOp base o s t)
    (hz : s.gpr .x17 = 0) : t.gpr .x17 = 0 :=
  (h.gpr _ (by decide)).trans hz

/-- **The addition**: slots 0–3 hold `mixedResult` of the accumulator and the entry, below
`2·p`; only slots 0–3 and 7–12 change. -/
theorem combAdd_ok {s : State} {base : Addr} (hs : Scr s base large) (hb : AccBel s.mem base) :
    WP isa (.block combAdd) s fun t => Keep base s t ∧ AccBel t.mem base ∧
      point (env t.mem base) 0 1 2 3 = Point64.mixedResult (env s.mem base 0) (env s.mem base 1)
        (env s.mem base 2) (env s.mem base 3) (env s.mem base 4) (env s.mem base 5)
        (env s.mem base 6) ∧
      ∀ i : Slot, (4 ≤ i.val ∧ i.val < 7) ∨ 13 ≤ i.val → fe t.mem base (offset i) = fe s.mem base (offset i) := by
  simp only [combAdd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (x17_ok s) fun a ⟨za, ka⟩ => ?_
  obtain k0 : Keep base s a := Keep.of_keeps ka (by decide)
  obtain ha := k0.scr hs
  obtain ea : env a.mem base = env s.mem base := by rw [ka.mem]
  obtain fa : ∀ i, fe a.mem base (offset i) = fe s.mem base (offset i) := fun i => by rw [ka.mem]
  -- t0 = 2z₁, t1 = y₁ - x₁, t2 = y₁ + x₁
  rw [WP.block_append_iff]
  refine WP.mono (addE ha 7 2 2 (by decide) (by decide) (by decide) za
    (by rw [fa]; exact hb 2 (by decide)) (by rw [fa]; exact hb 2 (by decide))) fun b1 ⟨h1, e1⟩ => ?_
  rw [ea] at e1
  obtain s1 := (h1.keep (by decide)).scr ha
  obtain z1 := h1.x17 za
  rw [WP.block_append_iff]
  refine WP.mono (subE s1 8 1 0 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 0 (by decide), fa]; exact hb 0 (by decide))) fun b2 ⟨h2, e2⟩ => ?_
  rw [e1] at e2
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e2
  obtain s2 := (h2.keep (by decide)).scr s1
  obtain z2 := h2.x17 z1
  rw [WP.block_append_iff]
  refine WP.mono (addE s2 9 1 0 (by decide) (by decide) (by decide) z2
    (by rw [fr h2 1 (by decide), fr h1 1 (by decide), fa]; exact hb 1 (by decide))
    (by rw [fr h2 0 (by decide), fr h1 0 (by decide), fa]; exact hb 0 (by decide)))
    fun b3 ⟨h3, e3⟩ => ?_
  rw [e2] at e3
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e3
  obtain s3 := (h3.keep (by decide)).scr s2
  obtain z3 := h3.x17 z2
  -- t3 = w₁ · kxy, t1 = t1 · ymx, t2 = t2 · xpy
  rw [WP.block_append_iff]
  refine WP.mono (mulE s3 10 3 6 (by decide) (by decide) (by decide) z3) fun b4 ⟨h4, l4, e4⟩ => ?_
  rw [e3] at e4
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e4
  obtain s4 := (h4.keep (by decide)).scr s3
  obtain z4 := h4.x17 z3
  rw [WP.block_append_iff]
  refine WP.mono (mulE s4 8 8 4 (by decide) (by decide) (by decide) z4) fun b5 ⟨h5, l5, e5⟩ => ?_
  rw [e4] at e5
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e5
  obtain s5 := (h5.keep (by decide)).scr s4
  obtain z5 := h5.x17 z4
  rw [WP.block_append_iff]
  refine WP.mono (mulE s5 9 9 5 (by decide) (by decide) (by decide) z5) fun b6 ⟨h6, l6, e6⟩ => ?_
  rw [e5] at e6
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e6
  obtain s6 := (h6.keep (by decide)).scr s5
  obtain z6 := h6.x17 z5
  -- t4 = t0 - t3, t0 = t0 + t3, t5 = t2 - t1, t1 = t2 + t1
  obtain l10 : fe b6.mem base (offset 10) < P2 := by
    rw [fr h6 10 (by decide), fr h5 10 (by decide)]; exact l4
  rw [WP.block_append_iff]
  refine WP.mono (subE s6 11 7 10 (by decide) (by decide) (by decide) z6 l10) fun b7 ⟨h7, e7⟩ => ?_
  rw [e6] at e7
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e7
  obtain s7 := (h7.keep (by decide)).scr s6
  obtain z7 := h7.x17 z6
  rw [WP.block_append_iff]
  refine WP.mono (addE1 s7 7 7 10 (by decide) (by decide) (by decide) z7
    (by rw [fr h7 10 (by decide)]; exact l10)) fun b8 ⟨h8, e8⟩ => ?_
  rw [e7] at e8
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e8
  obtain s8 := (h8.keep (by decide)).scr s7
  obtain z8 := h8.x17 z7
  obtain l8 : fe b8.mem base (offset 8) < P2 := by
    rw [fr h8 8 (by decide), fr h7 8 (by decide), fr h6 8 (by decide)]; exact l5
  obtain l9 : fe b8.mem base (offset 9) < P2 := by
    rw [fr h8 9 (by decide), fr h7 9 (by decide)]; exact l6
  rw [WP.block_append_iff]
  refine WP.mono (subE s8 12 9 8 (by decide) (by decide) (by decide) z8 l8) fun b9 ⟨h9, e9⟩ => ?_
  rw [e8] at e9
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e9
  obtain s9 := (h9.keep (by decide)).scr s8
  obtain z9 := h9.x17 z8
  rw [WP.block_append_iff]
  refine WP.mono (addE s9 8 9 8 (by decide) (by decide) (by decide) z9
    (by rw [fr h9 9 (by decide)]; exact l9) (by rw [fr h9 8 (by decide)]; exact l8))
    fun b10 ⟨h10, e10⟩ => ?_
  rw [e9] at e10
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e10
  obtain s10 := (h10.keep (by decide)).scr s9
  obtain z10 := h10.x17 z9
  -- z₃ = t4 · t0, x₃ = t5 · t4, y₃ = t0 · t1, w₃ = t5 · t1
  rw [WP.block_append_iff]
  refine WP.mono (mulE s10 2 11 7 (by decide) (by decide) (by decide) z10) fun b11 ⟨h11, l11, e11⟩ => ?_
  rw [e10] at e11
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e11
  obtain s11 := (h11.keep (by decide)).scr s10
  obtain z11 := h11.x17 z10
  rw [WP.block_append_iff]
  refine WP.mono (mulE s11 0 12 11 (by decide) (by decide) (by decide) z11) fun b12 ⟨h12, l12, e12⟩ => ?_
  rw [e11] at e12
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e12
  obtain s12 := (h12.keep (by decide)).scr s11
  obtain z12 := h12.x17 z11
  rw [WP.block_append_iff]
  refine WP.mono (mulE s12 1 7 8 (by decide) (by decide) (by decide) z12) fun b13 ⟨h13, l13, e13⟩ => ?_
  rw [e12] at e13
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e13
  obtain s13 := (h13.keep (by decide)).scr s12
  obtain z13 := h13.x17 z12
  refine WP.mono (mulE s13 3 12 8 (by decide) (by decide) (by decide) z13) fun t ⟨h14, l14, e14⟩ => ?_
  rw [e13] at e14
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e14
  obtain kt : Keep base s t := k0.trans (h1.keep (by decide))
    |>.trans (h2.keep (by decide))
    |>.trans (h3.keep (by decide))
    |>.trans (h4.keep (by decide))
    |>.trans (h5.keep (by decide))
    |>.trans (h6.keep (by decide))
    |>.trans (h7.keep (by decide))
    |>.trans (h8.keep (by decide))
    |>.trans (h9.keep (by decide))
    |>.trans (h10.keep (by decide))
    |>.trans (h11.keep (by decide))
    |>.trans (h12.keep (by decide))
    |>.trans (h13.keep (by decide))
    |>.trans (h14.keep (by decide))
  refine ⟨kt, ?_, ?_, ?_⟩
  · intro i hi
    obtain hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (by decide : ∀ i : Slot, i.val < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i hi
    rcases hc with rfl | rfl | rfl | rfl
    · rw [fr h14 0 (by decide), fr h13 0 (by decide)]; exact l12
    · rw [fr h14 1 (by decide)]; exact l13
    · rw [fr h14 2 (by decide), fr h13 2 (by decide), fr h12 2 (by decide)]; exact l11
    · exact l14
  · rw [e14]
    simp only [point, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    rfl
  · intro i hi
    obtain n : ∀ o : Slot, (o.val < 4 ∨ (7 ≤ o.val ∧ o.val ≤ 12)) → i ≠ o :=
      fun o ho e => by have := congrArg Fin.val e; omega_using [za, z1, z2, z3, l4, z4, l5, z5, l6, z6, l10, z7, z8, l8, l9, z9, z10, l11, z11, l12, z12, l13, z13, l14, hi, ho, this]
    rw [fr h14 i (n 3 (by decide)), fr h13 i (n 1 (by decide)), fr h12 i (n 0 (by decide)),
      fr h11 i (n 2 (by decide)), fr h10 i (n 8 (by decide)), fr h9 i (n 12 (by decide)),
      fr h8 i (n 7 (by decide)), fr h7 i (n 11 (by decide)), fr h6 i (n 9 (by decide)),
      fr h5 i (n 8 (by decide)), fr h4 i (n 10 (by decide)), fr h3 i (n 9 (by decide)),
      fr h2 i (n 8 (by decide)), fr h1 i (n 7 (by decide)), fa]

end VG.Proof.Ed25519.AArch64

end

end


/-!
# The comb's loop

`combNeg` negates the selected `2dT` under the sign's mask; `combAdd` adds it
(`combAdd_ok`), exactly as the specification's `pointAdd`, keeping the
accumulator's coordinates below `2·p` (`AccBel`). After step `i` of the loop, the accumulator
(slots 0–3) represents `[v + Σ_{i' < i} d_{i'} 16^{i'}]B` (`digitSum64`), from
`[v]B`; the loop starts at `[17 G]B` (`combStart`) and ends at the scalar's
multiple (`comb64_total`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open Word64 Fin.CommRing

/-! ## Frames -/

/-- Only the registers the comb uses (`x1`, `x19` and the field operations') and the field
slots change. -/
structure CombKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x19 → r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem CombKeep.trans {base : Addr} {s t u : State} (h : CombKeep base s t)
    (k : CombKeep base t u) : CombKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem CombKeep.scr {base : Addr} {s t : State} (h : CombKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem CombKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : CombKeep base s t :=
  ⟨fun r _ _ hc => h.gpr r hc, h.rd, h.wr, h.sp, h.mem⟩

theorem CombKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : CombKeep base s t := by
  refine ⟨fun r h19 h1 hc => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, by rw [h.mem]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact h19 h
  · exact h1 h
  · exact hc h

theorem CombKeep.bit {base : Addr} {s t : State} (h : CombKeep base s t) {q : Nat} (hq : q < 256) :
    t.mem (off base (768 + q)) = s.mem (off base (768 + q)) :=
  h.mem _ (by rw [ofs_off' base (by omega_using [hq])]; omega_using [])

theorem CombKeep.powers {base : Addr} {s t : State} (h : CombKeep base s t) :
    PowersKeep base 56 968 s t :=
  ⟨fun r a b c => h.gpr r a b c, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

/-! ## The negations -/

/-- `x4`–`x7` kept where the sign's mask in `x1` is set, else `x12`–`x15`. -/
theorem negSel_ok (s : State) {sg : Bool} (h1 : s.gpr .x1 = mask sg) :
    WP isa (.block negSel) s fun t =>
      t.gpr .x4 = (if sg then s.gpr .x4 else s.gpr .x12) ∧ t.gpr .x5 = (if sg then s.gpr .x5 else s.gpr .x13) ∧
      t.gpr .x6 = (if sg then s.gpr .x6 else s.gpr .x14) ∧ t.gpr .x7 = (if sg then s.gpr .x7 else s.gpr .x15) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  cases sg <;>
  · simp only [negSel, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', CondCode.holds,
      h1, mask, BitVec.and_self, Bool.false_eq_true, RegUpd.zf_write, decide_true, decide_false,
      show (BitVec.allOnes 64 = 0) = False by decide, Bool.not_false, Bool.not_true]
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ↓reduceIte]

/-- The loop's invariant, after `j` steps from `[v]B`. -/
structure CombInv (s₀ : State) (base : Addr) (S : Nat) (v : ℤ) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  acc : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum64 S j) • baseAff)
  bel : AccBel s.mem base
  keep : CombKeep base s₀ s

private theorem next_fact : ∀ j < 64,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 64 != 0) = decide (j + 1 ≠ 64) := by decide +kernel

theorem combNext_ok (s : State) {j : Nat} (hj : j < 64) (h : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ 64) ∧
      Keeps [.x19, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 1 < 4096 by decide),
    exec_subImm_x (show 64 < 4096 by decide), read_x, RegUpd.gpr_write, BitVec.setWidth_eq, h,
    (next_fact j hj).1, (next_fact j hj).2, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem combStep_ok {s₀ s : State} {base T : Addr} {S : Nat} {v : ℤ} {j : Nat}
    (h : CombInv s₀ base S v j s) (htb : TblAt s₀ base T) (hT : s.syms combSym = T)
    (hj : j < 64) :
    WP isa combStep s fun t => (t.gpr .x8 != 0) = decide (j + 1 ≠ 64) ∧
      CombInv s₀ base S v (j + 1) t := by
  rw [combStep]
  obtain hn := nib_lt S j
  -- The digit's magnitude and sign.
  refine WP.seq (WP.mono_syms (combDigitS_ok h.scratch (i := j) hj h.counter h.bits)
    fun a ⟨a2, a1, ka⟩ sya => ?_)
  obtain hsa : Scr a base := h.scratch.of_keeps ka (by decide)
  obtain a19 : a.gpr .x19 = BitVec.ofNat 64 j := (ka.gpr _ (by decide)).trans h.counter
  obtain ksa : CombKeep base s a := CombKeep.of_keeps ka (by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hr))
  -- The entry, negated for a negative digit.
  obtain hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr, h.keep.rd, h.keep.wr])
    (fun x hx => by rw [ka.mem]; exact h.keep.mem x (Or.inr (by omega_using [hx])))
  refine WP.seq (WP.mono (combEntry_ok hsa hta (by rw [sya]; exact hT) hj a19 (mag_lt hn) a2 a1)
    fun c ⟨c4, c5, c6, cf, kc⟩ => ?_)
  obtain fc : ∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → fe c.mem base (offset i) = fe s.mem base (offset i) :=
    fun i hi => by
      rw [cf.fe (by simp only [offset]; omega_using [hi]) (by simp only [offset]; omega_using []), ka.mem]
  obtain ec : ∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → env c.mem base i = env s.mem base i := fun i hi => by
    simp only [env, F]
    rw [fc i hi]
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry64_ok j (nib S j) hj hn
  obtain c21 : env c.mem base 21 = 0 := (ec 21 (by decide)).trans h.zero
  obtain cq : cachedAt (env c.mem base) 4 5 6 = cache q := by
    rw [← hq]
    obtain hT := combCached64_T j (mag (nib S j))
    by_cases hlt : nib S j < 8
    · simp only [hlt, decide_true, ↓reduceIte] at c4 c5 c6 ⊢
      simp only [cachedAt, negCached, c4, c5, c6, hT]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at c4 c5 c6 ⊢
      rw [cachedAt_eq hT c4 c5 c6]
  obtain hsc := kc.scr hsa
  obtain c19 : c.gpr .x19 = BitVec.ofNat 64 j := (kc.gpr _ (by decide)).trans a19
  obtain belc : AccBel c.mem base := fun i hi => by
    rw [fc i (.inl hi)]
    exact h.bel i hi
  -- Added.
  rw [WP.seq_iff]
  refine WP.mono (combAdd_ok hsc belc) fun d ⟨kd, beld, vd, md⟩ => ?_
  obtain d19 : d.gpr .x19 = BitVec.ofNat 64 j := (kd.gpr _ (by decide)).trans c19
  refine WP.mono (combNext_ok d hj d19) fun t ⟨t19, t8, kt⟩ => ⟨t8, ?_⟩
  obtain kbt : CombKeep base a t :=
    (((CombKeep.of_keep kc).trans (CombKeep.of_keep kd))).trans (CombKeep.of_keeps kt (by decide))
  obtain kst := ksa.trans kbt
  obtain pc : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide)]
  obtain d21 : env d.mem base 21 = env c.mem base 21 := by
    simp only [env, F]; rw [md 21 (.inr (by decide))]
  refine ⟨by omega_using [hj], kbt.scr hsa, t19, ?_, fun q hq => ?_, ?_, fun i hi => by rw [kt.mem]; exact beld i hi,
    h.keep.trans kst⟩
  · rw [kt.mem, d21]
    exact c21
  · rw [kst.bit hq]; exact h.bits q hq
  · have h4 : env c.mem base 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X cq
    obtain h5 : env c.mem base 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y cq
    obtain h6 : env c.mem base 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z cq
    rw [kt.mem, vd, h4, h5, h6]
    obtain e := Point64.mixedResult_eq (point (env c.mem base) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e]
    simp only [point] at pc
    rw [pc, digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc hrq

/-- The loop's steps from digit `j₀ < 64` on, from the invariant at `j₀`. -/
theorem combSteps_ok {s₀ b : State} {base T : Addr} (htb : TblAt s₀ base T) {S : Nat} {v : ℤ}
    {j₀ : Nat} (hj₀ : j₀ < 64) (init : CombInv s₀ base S v j₀ b) (hT : b.syms combSym = T) :
    WP isa (.loop combStep (.nonzero .x .x8)) b fun t => CombInv s₀ base S v 64 t := by
  apply WP.loop (fun n (t : State) => (CombInv s₀ base S v (64 - n) t ∧ t.syms combSym = T) ∧
    0 < n ∧ n ≤ 64) (n := 64 - j₀)
  · intro n t ⟨⟨ht, hty⟩, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_using [hn0]⟩
    refine WP.mono_syms (combStep_ok ht htb hty (by omega_using [])) fun u ⟨u8, hu⟩ suy => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by simp only [eval, read_x, u8, show 64 - (0 + 1) + 1 = 64 from rfl, ne_eq,
        not_true_eq_false, decide_false], hu⟩
    · refine Or.inr ⟨by simp only [eval, read_x, u8, show 64 - (k + 1) + 1 ≠ 64 by omega_using [hk], ne_eq,
        not_false_eq_true, decide_true], k, by omega_using [], ⟨?_, by rw [suy]; exact hty⟩, by omega_using [hk], by omega_using [hn]⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega_using [hn]]; exact hu
  · exact ⟨⟨by rw [show 64 - (64 - j₀) = j₀ by omega_using [hj₀]]; exact init, hT⟩, by omega_using [hj₀], by omega_using []⟩

/-- The counter `x19` set to `j < 2^16`. -/
theorem counterInit_ok (s : State) (j : Nat) (hj : j < 2 ^ 16) :
    WP isa (.block [.movz .w .x19 j 0]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Size.bits]
    simp only [Nat.mul_zero, Nat.shiftLeft_zero, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    omega_using [hj]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-- The loop from digit `j₀ < 64`, from `[v + Σ_{i < j₀} d_i 16^i]B`. -/
theorem combLoopFrom_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} {v : ℤ} {j₀ : Nat} (hj₀ : j₀ < 64)
    (hz : env s.mem base 21 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hv : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum64 S j₀) • baseAff))
    (hB : AccBel s.mem base) :
    WP isa (combLoopFrom j₀) s fun t => CombInv s base S v 64 t := by
  rw [combLoopFrom]
  refine WP.seq (WP.mono_syms (counterInit_ok s j₀ (by omega_using [hj₀])) fun b ⟨b19, kb⟩ syb => ?_)
  obtain ksb : CombKeep base s b := CombKeep.of_keeps kb (by decide)
  exact combSteps_ok htb hj₀
    ⟨by omega_using [hj₀], hs.of_keeps kb (by decide), b19, by rw [kb.mem]; exact hz,
      fun q hq => by rw [kb.mem]; exact hb q hq, by rw [kb.mem]; exact hv,
      fun i hi => by rw [kb.mem]; exact hB i hi, ksb⟩
    (by rw [syb]; exact hT)

/-- The loop over the 64 digits, from `[v]B`. -/
theorem combLoop_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} {v : ℤ}
    (hz : env s.mem base 21 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hv : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff)) (hB : AccBel s.mem base) :
    WP isa combLoop s fun t => CombInv s base S v 64 t :=
  combLoopFrom_ok hs htb hT (by decide) hz hb (by rw [digitSum64, add_zero]; exact hv) hB

/-! ## The comb -/

theorem combInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combInit) s fun t => CombKeep base s t ∧ env t.mem base 21 = 0 ∧
      point (env t.mem base) 0 1 2 3 = combStart ∧ AccBel t.mem base := by
  refine WP.mono (fieldCode_okS _ hs (Small.none s.mem base)) fun t ⟨kt, vt, st⟩ =>
    ⟨CombKeep.of_keep kt, ?_, ?_, fun i hi => ?_⟩
  · rw [vt]; rfl
  · rw [vt]; rfl
  · have := st i ((by decide : ∀ i : Slot, i.val < 4 →
      smallAfterOps ([.const 21 0] ++ constPointOps combStart) (fun _ => false) i = true) i hi)
    simp only [VG.Proof.X25519.AArch64.AltLadder.P2]; omega_using [this]

theorem combMultiply_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono_syms (combInit_ok hs) fun a ⟨ka, az, ap, ab⟩ sya => ?_)
  obtain hsa := ka.scr hs
  obtain hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr])
    (fun x hx => ka.mem x (Or.inr (by omega_using [hx])))
  obtain hv : Rep (point (env a.mem base) 0 1 2 3) (((17 * combGVal : Nat) : ℤ) • baseAff) := by
    rw [ap, natCast_zsmul]; exact combStart_ok
  refine WP.mono (combLoop_ok hsa hta (by rw [sya]; exact hT) az
    (fun q hq => by rw [ka.bit hq]; exact hb q hq) hv ab) fun t ht => ⟨?_, ka.trans ht.keep⟩
  have hu := ht.acc
  rw [comb64_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64

end

end

/-! The scalar bits, base-point multiplication, and canonical encoding compose. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodedValue p) := rfl

theorem encodedValue_rep {p q : Spec.Ed25519.Point} {a : Edwards.EPoint dZ} (hp : Rep p a)
    (hq : Rep q a) : encodedValue p = encodedValue q := by
  rw [encodedValue, encodedValue, hp.affine_x, hp.affine_y, hq.affine_x, hq.affine_y]

theorem powersKeep_outside {base : Addr} {s t : State} (h : PowersKeep base 56 968 s t) :
    Outside base 56 968 s.mem t.mem := fun p hp => h.mem p (by omega_using [hp]) hp

theorem scalarBasePrepare_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBasePrepare s fun t => PowersKeep base 56 968 s t ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2)) ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
  rw [scalarBasePrepare]
  refine WP.mono (expandScalarBits_ok hs hp 32 (by decide) (by decide) hr hd) fun a ⟨ka, abits⟩ => ?_
  have kap : PowersKeep base 56 968 s a := by
    refine ⟨fun r hb _ hr => ka.gpr r (fun hm => ?_), ka.rd, ka.wr, ka.sp,
      (TableFrame.table ka.mem).mono (by decide) (by decide)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hb rfl
    · exact hr (by decide)
  have hscalar : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt s.mem k 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at h
    rw [show 256 ^ 32 = 2 ^ (16 * 16) by decide] at h
    exact h
  exact ⟨kap, abits, hscalar⟩

theorem scalarBaseEngine_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} {base k T : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) (htb : TblAt s base T) (hT : s.syms combSym = T) :
    WP isa scalarBaseEngine s fun t => PowersKeep base 56 968 s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBaseEngine]
  refine WP.seq (WP.mono_syms (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, bbits, hscalar⟩ syb => ?_)
  have hbt : TblAt b base T := htb.of_far (by rw [kab.rd, kab.wr])
    (fun x hx => (powersKeep_outside kab) x (Or.inr (by omega_using [hx])))
  refine WP.seq (WP.mono (combMultiply_ok (kab.scratch hs) hbt (by rw [syb]; exact hT)
    (by simpa using hscalar) bbits)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scr (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc.powers).trans
    ⟨fun r hb _ hr => kt.gpr r hr hb, kt.rd, kt.wr, kt.sp, TableFrame.workspace kt.mem⟩, ?_⟩
  change val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv]
  exact encodedValue_rep cp (pointMul_rep _ basePoint_rep)

end VG.Proof.Ed25519.AArch64
