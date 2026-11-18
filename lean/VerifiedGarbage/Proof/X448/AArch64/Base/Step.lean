module

import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.X448.AArch64.Fast.Bounds
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.BaseAdd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Mem
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
public import VerifiedGarbage.Proof.X448.AArch64.Base.Digit
import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.X448.AArch64.Base.Comb
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Curve448.AArch64.Swap

/-! ### `X448.AArch64.Base.Negate`, which this module and modules that import it used -/

section

/-! ### `X448.AArch64.Base.Select`, which this module and modules that import it used -/

section

/-!
# X448 of the base point on AArch64: the constant-time selection

Untrusted: everything here is checked by Lean. As Ed25519's comb
(`Proof/Ed25519/AArch64/CombSelect.lean`): with `oddReg m` (`evenReg m`) all
ones exactly for `m` the odd (even) digit's magnitude, and `x5` (`x0`) the bit
of a zero magnitude, `selectWord` loads every candidate's limb from the table
once, ANDs it with both digits' masks and ORs it into `x1` and `x2`, so only
each digit's candidate survives, and stores them. The tables are at `T`
(`TblAt`): readable, beyond the working space, word `i` the static's
`combWord i`. Nothing here unfolds a table: each lemma holds for any words.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside2 ofs store_ok word_write writeW_outside)
open VG.Proof.Curve448.AArch64 (mask)

private theorem odd_regs : ∀ m < 9, oddReg m ∉ [Reg.x6, .x7, .x1, .x2] := by decide
private theorem even_regs : ∀ m < 9, evenReg m ∉ [Reg.x6, .x7, .x1, .x2] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

/-- The comb's tables at `T`: readable, beyond the working space at `base`, word `i` the
static's (`combWord i`). -/
structure TblAt (s : State) (base T : Addr) : Prop where
  rd : InRegions (s.rd ++ s.wr) T (8 * (57 * 128))
  far : ∀ i < 8 * (57 * 128), 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 57 * 128, s.mem.read (T + BitVec.ofNat 64 (8 * i)) 8 = combWord i

theorem tbl_add (T : Addr) (a b : Nat) :
    T + BitVec.ofNat 64 a + BitVec.ofNat 64 b = T + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The tables survive what keeps the regions and the memory beyond the working space. -/
theorem TblAt.of_far {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    TblAt t base T :=
  ⟨hrw ▸ h.rd, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.read_congr fun b hb => hm _ ?_
    rw [tbl_add T _ _]
    exact h.far _ (by omega_arith)⟩

/-- The tables, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem CombHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : CombHeld s wr)
    (hrd : (⟨s.syms combSym, 8 * combWords.length⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : TblAt s base (s.syms combSym) := by
  obtain ⟨held, fit, dj⟩ := h
  rw [combWords_length] at held fit dj hrd
  have hc : Region.Contains ⟨s.syms combSym, 8 * (57 * 128)⟩ (s.syms combSym) (8 * (57 * 128)) := by
    have := Offset.contains_base (s.syms combSym) (d := 0) (n := 8 * (57 * 128)) (k := 8 * (57 * 128))
      (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨_, hrd, hc⟩, fun i hi => ?_, fun i hi => ?_⟩
  · refine Nat.le_of_not_lt fun hlt => dj _ hsc _
      (Offset.contains_base _ (d := i) (n := 1) (k := 8 * (57 * 128)) (by omega_arith) (by omega_arith)) ?_
    simp only [Region.Contains]; simp only [ofs] at hlt; omega_arith
  · rw [← combWords_getD hi, ← held i hi]
    exact (BitVec.setWidth_eq _).symm

/-- One candidate's limb: loaded into `x6` from `x9 + d`, masked into `x1` (odd) and `x2`
(even). -/
def candCode (d m : Nat) : List Instr :=
  [.ldr .x .x6 .x9 d, .logic .and .x .x7 .x6 (oddReg m), .logic .orr .x .x1 .x1 .x7,
    .logic .and .x .x7 .x6 (evenReg m), .logic .orr .x .x2 .x2 .x7]

theorem cand_ok (s : State) {v : BitVec 64} {m d : Nat} (hm : m < 9) (hd : d % 8 = 0 ∧ d < 4096 * 8)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 d) 8)
    (hv : s.mem.read (s.gpr .x9 + BitVec.ofNat 64 d) 8 = v) :
    WP isa (.block (candCode d m)) s fun t =>
      t.gpr .x1 = s.gpr .x1 ||| (v &&& s.gpr (oddReg m)) ∧
      t.gpr .x2 = s.gpr .x2 ||| (v &&& s.gpr (evenReg m)) ∧
      Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  have ho := odd_regs m hm
  have he := even_regs m hm
  have ho6 := ne_of_not_mem ho (r' := .x6) (by decide)
  have he6 := ne_of_not_mem he (r' := .x6) (by decide)
  have he7 := ne_of_not_mem he (r' := .x7) (by decide)
  have he1 := ne_of_not_mem he (r' := .x1) (by decide)
  apply WP.of_runBlock
  simp only [candCode, runBlock_cons, runStep_some, runBlock_nil, exec, addr, hd, and_self, ite_true,
    Option.bind_some, State.load, hr, Option.map_some, State.read, Size.bits, Size.bytes,
    RegUpd.gpr_write, BitVec.setWidth_eq, ho6, he6, he7, he1, ite_true, ite_false,
    reduceCtorEq, hv, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- Limb `w` of `vs[a]` after the candidates `m ≤ n`, zero if `a > n`. -/
def selWord (vs : List Spec.X448.Fe) (a n w : Nat) : BitVec 64 :=
  if a ≤ n then limb (vs.getD a 0) w else 0

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp

theorem sel_step (vs : List Spec.X448.Fe) (a n w : Nat) :
    selWord vs a n w ||| (limb (vs.getD (n + 1) 0) w &&& mask (decide (a = n + 1))) =
      selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a ≤ n
  · simp only [h, ↓reduceIte, show a ≤ n + 1 by omega_arith, show ¬ a = n + 1 by omega_arith, decide_false,
      mask, Bool.false_eq_true]
    exact or_and_zero _ _
  · by_cases he : a = n + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, mask, BitVec.and_allOnes]
      exact BitVec.zero_or
    · simp only [h, he, ↓reduceIte, show ¬ a ≤ n + 1 by omega_arith, decide_false, mask,
        Bool.false_eq_true]
      exact or_and_zero _ _

/-- The masks of both digits, for the magnitudes `ao` and `ae`. -/
def Masks (ao ae : Nat) (s : State) : Prop :=
  (∀ m, 1 ≤ m → m ≤ 8 → s.gpr (oddReg m) = mask (decide (ao = m))) ∧
  (∀ m, 1 ≤ m → m ≤ 8 → s.gpr (evenReg m) = mask (decide (ae = m))) ∧
  s.gpr .x5 = zeroBit ao ∧ s.gpr .x0 = zeroBit ae

private theorem odd_regs9 : ∀ m < 9, oddReg m ∉ [Reg.x9, .x8, .x6, .x7, .x1, .x2] := by decide
private theorem even_regs9 : ∀ m < 9, evenReg m ∉ [Reg.x9, .x8, .x6, .x7, .x1, .x2] := by decide

theorem Masks.of_keeps {ao ae : Nat} {rs : List Reg} {s t : State} (h : Masks ao ae s)
    (k : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ [Reg.x9, .x8, .x6, .x7, .x1, .x2] := by simp) :
    Masks ao ae t := by
  have nm : ∀ r, r ∉ [Reg.x9, .x8, .x6, .x7, .x1, .x2] → r ∉ rs := fun r hr hm => hr (hrs r hm)
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, ?_, ?_⟩
  · rw [k.1 _ (nm _ (odd_regs9 j (by omega_arith)))]; exact h.1 j h1 h8
  · rw [k.1 _ (nm _ (even_regs9 j (by omega_arith)))]; exact h.2.1 j h1 h8
  · rw [k.1 _ (nm _ (by decide))]; exact h.2.2.1
  · rw [k.1 _ (nm _ (by decide))]; exact h.2.2.2

/-- The candidates' limbs `w` of the table at `x9`: entry `m + 1`'s at `c + 64 m + 8 w`. -/
def Cands (s : State) (vs : List Spec.X448.Fe) (c w : Nat) : Prop :=
  ∀ m < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (c + 64 * m + 8 * w)) 8 ∧
    s.mem.read (s.gpr .x9 + BitVec.ofNat 64 (c + 64 * m + 8 * w)) 8 = limb (vs.getD (m + 1) 0) w

theorem Cands.of_keeps {s t : State} {vs : List Spec.X448.Fe} {c w : Nat} (h : Cands s vs c w)
    (k : Keeps [.x6, .x7, .x1, .x2] s t) (hm : t.mem = s.mem) : Cands t vs c w := fun m hm' => by
  rw [k.1 .x9 (by decide), k.2.1, k.2.2, hm]; exact h m hm'

theorem cands_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s)
    (vs : List Spec.X448.Fe) {c w : Nat} (hc : c ≤ 512 ∧ c % 8 = 0) (hw : w < 8) (ht : Cands s vs c w)
    (n : Nat) (hn : n ≤ 8)
    (h0 : s.gpr .x1 = selWord vs ao 0 w ∧ s.gpr .x2 = selWord vs ae 0 w) :
    WP isa (.block ((List.range n).flatMap fun m => candCode (c + 64 * m + 8 * w) (m + 1))) s
      fun t => t.gpr .x1 = selWord vs ao n w ∧ t.gpr .x2 = selWord vs ae n w ∧
        Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨h0.1, h0.2, ⟨fun _ _ => rfl, rfl, rfl⟩, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨t1, t2, kt, mt⟩ => ?_
    have tm := hm.of_keeps kt
    obtain ⟨hr, hv⟩ := ht.of_keeps kt mt n (by omega_arith)
    refine WP.mono (cand_ok t (by omega_arith : n + 1 < 9) ⟨by omega_arith, by omega_arith⟩ hr hv)
      fun u ⟨u1, u2, ku, mu⟩ => ⟨?_, ?_, kt.trans ku, mu.trans mt⟩
    · rw [u1, t1, tm.1 (n + 1) (by omega_arith) (by omega_arith), sel_step]
    · rw [u2, t2, tm.2.1 (n + 1) (by omega_arith) (by omega_arith), sel_step]

private theorem movz0 : (((0 : BitVec 16).setWidth 32).setWidth 64) = 0 := by decide

private theorem limb_one_zero : ∀ w < 8, ∀ one : Bool,
    (if (one && w == 0) = true then (1 : BitVec 64) else 0) =
      limb (if one then 1 else 0) w := by
  decide +kernel

/-- The start of word `w`'s selections: `1` for `|d| = 0` in limb 0 of `y`'s identity (`one`). -/
def startCode (one : Bool) (w : Nat) : List Instr :=
  if one && w == 0 then [.addImm .x .x1 .x5 0, .addImm .x .x2 .x0 0]
  else [.movz .w .x1 0 0, .movz .w .x2 0 0]

theorem start_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s) (one : Bool)
    (vs : List Spec.X448.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0) (w : Nat) (hw : w < 8) :
    WP isa (.block (startCode one w)) s fun t =>
      t.gpr .x1 = selWord vs ao 0 w ∧ t.gpr .x2 = selWord vs ae 0 w ∧
        Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  have hz : ∀ a, (if (one && w == 0) = true then zeroBit a else 0) = selWord vs a 0 w := fun a => by
    unfold selWord zeroBit
    by_cases ha : a = 0
    · subst ha
      simp only [Nat.le_refl, ↓reduceIte, h0]
      exact limb_one_zero w hw one
    · simp [ha, show ¬ a ≤ 0 by omega_arith]
  rw [← hz ao, ← hz ae]
  unfold startCode
  by_cases h : (one && w == 0) = true
  · simp only [h, ↓reduceIte]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
      ite_true, ite_false, reduceCtorEq, hm.2.2.1, hm.2.2.2, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, RegUpd.gpr_write, ite_false, reduceCtorEq,
      Nat.mul_zero, BitVec.shiftLeft_zero, movz0, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]

/-- The offset of the coordinate's candidates in a table: `y`'s after `x`'s. -/
abbrev coordOff (one : Bool) : Nat := if one then 512 else 0

theorem coordOff_le (one : Bool) : coordOff one ≤ 512 ∧ coordOff one % 8 = 0 := by
  cases one <;> decide

theorem selectWord_eq (one : Bool) (o e w : Nat) :
    selectWord one o e w = startCode one w ++
      ((List.range 8).flatMap fun m => candCode (coordOff one + 64 * m + 8 * w) (m + 1)) ++
      [st .x1 (o + 8 * w), st .x2 (e + 8 * w)] := rfl

theorem word_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hm : Masks ao ae s)
    (one : Bool) (vs : List Spec.X448.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hb : o + 64 ≤ 8192) (hbe : e + 64 ≤ 8192)
    (w : Nat) (hw : w < 8) (ht : Cands s vs (coordOff one) w) :
    WP isa (.block (selectWord one o e w)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 8 * w)) (selWord vs ao 8 w)).writeW (off base (e + 8 * w))
        (selWord vs ae 8 w) ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  rw [selectWord_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (start_ok s hm one vs h0 w hw) fun a ⟨a1, a2, ka, ma⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cands_ok a (hm.of_keeps ka) vs (coordOff_le one) hw (ht.of_keeps ka ma) 8
    (le_refl _) ⟨a1, a2⟩) fun b ⟨b1, b2, kb, mb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  rw [show ([st .x1 (o + 8 * w), st .x2 (e + 8 * w)] : List Instr) =
    [st .x1 (o + 8 * w)] ++ [st .x2 (e + 8 * w)] from rfl, WP.block_append_iff]
  refine WP.mono (store_ok hsb (by omega_arith) (by omega_arith) .x1) fun c ⟨mc, kc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (store_ok hsc (by omega_arith) (by omega_arith) .x2) fun t ⟨mt, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, mc, kc.1 _ (by decide), b1, b2, mb, ma]
  · exact ((ka.trans kb).trans (kc.mono (by simp))).trans (kt.mono (by simp))

/-- The candidates of every word, beyond the working space at `base`. -/
def CandsFar (s : State) (base : Addr) (vs : List Spec.X448.Fe) (c : Nat) : Prop :=
  ∀ w < 8, Cands s vs c w ∧ ∀ m < 8, ∀ b < 8,
    8192 ≤ ofs base (s.gpr .x9 + BitVec.ofNat 64 (c + 64 * m + 8 * w) + BitVec.ofNat 64 b)

/-- The candidates survive the registers' and the working space's changes. -/
theorem CandsFar.of_outside2 {s t : State} {base : Addr} {vs : List Spec.X448.Fe} {c : Nat}
    (h : CandsFar s base vs c) (k : Keeps [.x6, .x7, .x1, .x2] s t) {o e : Nat} (hb : o + 64 ≤ 8192)
    (hbe : e + 64 ≤ 8192) (hm : Outside2 base o 64 e 64 s.mem t.mem) : CandsFar t base vs c :=
  fun w hw => by
    obtain ⟨hc, hf⟩ := h w hw
    refine ⟨fun m hm' => ?_, by rw [k.1 .x9 (by decide)]; exact hf⟩
    obtain ⟨hr, hv⟩ := hc m hm'
    rw [k.1 .x9 (by decide), k.2.1, k.2.2]
    refine ⟨hr, ?_⟩
    rw [← hv]
    exact Mem.read_congr fun b hb' => hm _ (by have := hf m hm' b hb'; omega_arith)
      (by have := hf m hm' b hb'; omega_arith)

theorem fieldPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat}
    (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X448.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 64 ≤ e ∨ e + 64 ≤ o)
    (hb : o + 64 ≤ 8192) (hbe : e + 64 ≤ 8192) (hc : CandsFar s base vs (coordOff one)) (n : Nat)
    (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord one o e w)) s fun t =>
      (∀ w < n, word t.mem base (o + 8 * w) = selWord vs ao 8 w ∧
        word t.mem base (e + 8 * w) = selWord vs ae 8 w) ∧
      Outside2 base o 64 e 64 s.mem t.mem ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨tv, tf, kt⟩ => ?_
    have ht : Scr t base := hs.of_keeps kt (by decide)
    refine WP.mono (word_ok ht (hm.of_keeps kt) one vs h0 ho he hb hbe n (by omega_arith)
      ((hc.of_outside2 kt hb hbe tf) n (by omega_arith)).1)
      fun u ⟨um, ku⟩ => ⟨fun w hw => ?_, ?_, kt.trans ku⟩
    · rw [um, VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases hwn : w = n
      · subst hwn
        simp only [↓reduceIte, show o + 8 * w ≠ e + 8 * w by omega_arith]
        exact ⟨trivial, trivial⟩
      · simp only [show o + 8 * w ≠ e + 8 * n by omega_arith, show o + 8 * w ≠ o + 8 * n by omega_arith,
          show e + 8 * w ≠ e + 8 * n by omega_arith, show e + 8 * w ≠ o + 8 * n by omega_arith, ↓reduceIte]
        exact tv w (by omega_arith)
    · rw [um]
      refine fun x h1 h2 => ?_
      rw [show ((t.mem.writeW (off base (o + 8 * n)) (selWord vs ao 8 n)).writeW (off base (e + 8 * n))
          (selWord vs ae 8 n)) x = t.mem x from ?_]
      · exact tf x h1 h2
      · rw [VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
          VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]

/-! ## The selected field's value -/

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) :
    (((List.range 9).map (Impl.X448.baseTable j)).map f).getD a 0 = f (Impl.X448.baseTable j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

/-- `x9` = table `j`'s address, from the static's and `x19 = j`. -/
theorem tblAddr_ok (s : State) {T : Addr} (hT : s.syms combSym = T) {j : Nat} (hj : j < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block tblAddr) s fun t =>
      t.gpr .x9 = T + BitVec.ofNat 64 (1024 * j) ∧ Keeps [.x9, .x8] s t ∧ t.mem = s.mem := by
  have hsh : BitVec.ofNat 64 j <<< 10 = BitVec.ofNat 64 (1024 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 1024 * j < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show j * 2 ^ 10 < 2 ^ 64 by omega_arith)]
    omega_arith
  apply WP.of_runBlock
  simp only [tblAddr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 10 < 64 from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, hc, hT, hsh, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Table `j`'s candidates for a coordinate (`f`), from the tables at `T`. -/
theorem candsFar_of_tbl {s : State} {base T : Addr} (h : TblAt s base T) {j : Nat} (hj : j < 57)
    (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (1024 * j)) (one : Bool) :
    CandsFar s base (((List.range 9).map (Impl.X448.baseTable j)).map
      (if one then Prod.snd else Prod.fst)) (coordOff one) := fun w hw => by
  -- Word `w` of entry `m + 1` is word `i` of the tables.
  have addr : ∀ m < 8, ∀ b < 8, s.gpr .x9 + BitVec.ofNat 64 (coordOff one + 64 * m + 8 * w) +
      BitVec.ofNat 64 b =
      T + BitVec.ofNat 64 (8 * (128 * j + coordOff one / 8 + 8 * m + w) + b) := fun m hm b hb => by
    have := (coordOff_le one)
    rw [hx9, tbl_add T _ _, tbl_add T _ _]
    congr 2
    omega_arith
  refine ⟨fun m hm => ?_, fun m hm b hb => ?_⟩
  · have := (coordOff_le one)
    have hi : 128 * j + coordOff one / 8 + 8 * m + w < 57 * 128 := by omega_arith
    have a0 := addr m hm 0 (by decide)
    rw [BitVec.add_zero, Nat.add_zero] at a0
    rw [a0]
    refine ⟨VG.CallLay.inRegions_sub h.rd (by omega_arith) (by decide), ?_⟩
    rw [h.val _ hi, combWord, entries_getD j (m + 1) (by omega_arith)]
    have e1 : (128 * j + coordOff one / 8 + 8 * m + w) / 128 = j := by omega_arith
    have e2 : (128 * j + coordOff one / 8 + 8 * m + w) % 64 / 8 + 1 = m + 1 := by
      cases one <;> simp only [coordOff, Bool.false_eq_true, ↓reduceIte] <;> omega_arith
    have e3 : (128 * j + coordOff one / 8 + 8 * m + w) % 8 = w := by
      cases one <;> simp only [coordOff, Bool.false_eq_true, ↓reduceIte] <;> omega_arith
    simp only [e1, e2, e3]
    cases one
    · simp only [coordOff, Bool.false_eq_true, ↓reduceIte, show (128 * j + 0 / 8 + 8 * m + w) % 128 < 64 by omega_arith]
    · simp only [coordOff, ↓reduceIte, show ¬ (128 * j + 512 / 8 + 8 * m + w) % 128 < 64 by omega_arith]
  · rw [addr m hm b hb]
    have := (coordOff_le one)
    exact h.far _ (by omega_arith)

/-- **Table `j`'s entries** for both digits, `|d| = ao` and `ae`, to slots 6–9, limb by limb. -/
theorem select_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {j : Nat} (hj : j < 57) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks ao ae s) :
    WP isa (.block select) s fun t =>
      (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
        word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
        word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
        word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
      VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x9, .x8, .x6, .x7, .x1, .x2] s t := by
  rw [select, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tblAddr_ok s hT hj hc) fun a ⟨a9, ka, ma⟩ => ?_
  have hsa : Scr a base := hs.of_keeps ka (by decide)
  have hta : TblAt a base T := htb.of_far (by rw [ka.2.1, ka.2.2]) (fun x _ => by rw [ma])
  rw [WP.block_append_iff]
  refine WP.mono (fieldPrefix_ok hsa (hm.of_keeps ka) false _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := OX) (e := EX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (candsFar_of_tbl hta hj a9 false) 8 (le_refl _))
    fun b ⟨bv, bf, kb⟩ => ?_
  have hsb : Scr b base := hsa.of_keeps kb (by decide)
  have hcb : CandsFar b base _ (coordOff true) :=
    (candsFar_of_tbl hta hj a9 true).of_outside2 kb (by decide) (by decide) bf
  refine WP.mono (fieldPrefix_ok hsb ((hm.of_keeps ka).of_keeps kb) true _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := OY) (e := EY) (by decide) (by decide) (by decide) (by decide) (by decide) hcb 8 (le_refl _))
    fun t ⟨tv, tf, kt⟩ => ⟨fun w hw => ?_, ?_, (ka.mono (by simp)).trans ((kb.trans kt).mono (by simp))⟩
  · obtain ⟨b1, b2⟩ := bv w hw
    obtain ⟨t1, t2⟩ := tv w hw
    have sel : ∀ (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) (a : Nat), a < 9 →
        selWord (((List.range 9).map (Impl.X448.baseTable j)).map f) a 8 w =
          limb (f (Impl.X448.baseTable j a)) w := fun f a ha => by
      unfold selWord; rw [ite_eq_left (by omega_arith), entries_getD j a ha]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tf.word (by simp only [OX, OY, slot]; omega_arith) (by simp only [OX, EY, slot]; omega_arith)
        (by simp only [OX, slot]; omega_arith), b1, sel _ _ hao]; rfl
    · rw [tf.word (by simp only [EX, OY, slot]; omega_arith) (by simp only [EX, EY, slot]; omega_arith)
        (by simp only [EX, slot]; omega_arith), b2, sel _ _ hae]; rfl
    · rw [t1, sel _ _ hao]; rfl
    · rw [t2, sel _ _ hae]; rfl
  · intro x hx
    rw [tf x (by simp only [OX, OY, slot] at hx ⊢; omega_arith) (by simp only [OX, EY, slot] at hx ⊢; omega_arith),
      bf x (by simp only [OX, slot] at hx ⊢; omega_arith) (by simp only [OX, EX, slot] at hx ⊢; omega_arith), ma]

/-- What a selection leaves: table `j`'s entries for both digits in slots 6–9. -/
def Selected (base : Addr) (j ao ae : Nat) (s t : State) : Prop :=
  (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
    word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
    word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
    word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
  VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x9, .x8, .x6, .x7, .x1, .x2] s t

end VG.Proof.X448.AArch64.Base

end

end

/-!
# X448 of the base point on AArch64: negating an entry for a negative digit

Untrusted: everything here is checked by Lean. `negate ox o w` computes
`0 - x` into slot `w`, loads the top bit of the digit's nibble (`n < 8` exactly
if it is clear) as a mask, and swaps `x` with `0 - x` under it, as Ed25519's
comb negates its cached entries.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs contains_sc read1_eq)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib nib_bits)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem bit_mask : ∀ b < 2,
    ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 =
      VG.Proof.X448.AArch64.mask (decide (b = 0)) := by
  decide

theorem nib_neg (k i : Nat) : decide (nib k i < 8) = decide ((k / 2 ^ (4 * i + 3)) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (k / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have h1 := Nat.mod_lt (k / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have h2 := Nat.mod_lt (k / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have h3 := Nat.mod_lt (k / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  apply decide_eq_decide.mpr
  omega_using []

private theorem index3_fact : ∀ j < 57, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) {n k j i o : Nat} (hn : n ≤ 57)
    (hj : j < 57) (hi : i < 2 * n) (hoi : 8 * j + o = BITS + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hb : Bits n base k s.mem) :
    WP isa (.block [.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (o + 3),
      .subImm .x .x6 .x6 1]) s fun t =>
      t.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (nib k i < 8)) ∧ Keeps [.x6] s t ∧
        t.mem = s.mem := by
  have hr : InRegions (s.rd ++ s.wr) (off base (BITS + (4 * i + 3))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [hn, hi])⟩
  have he : base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (o + 3) = off base (BITS + (4 * i + 3)) := by
    simp only [off]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (base + ·) (congrArg (BitVec.ofNat 64) (by omega_using [hoi]))
  have hv := bit_mask _ (Nat.mod_lt (k / 2 ^ (4 * i + 3)) (show 2 > 0 by decide))
  rw [← nib_neg, ← bit_eq, ← hb _ (by omega_using [hi])] at hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, addr, Size.bits,
    show (3 : Nat) < 64 from by decide, show (1 : Nat) < 4096 from by decide,
    show o + 3 < 4096 * 1 by omega_using [ho], Nat.mod_one, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hc, index3_fact j hj, hs.x3, he, hr, read1_eq, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X448.AArch64.ofs base (off base d) = d := by
  have := VG.Proof.X448.AArch64.ofs_off base (d := d) (i := 0) (by omega_using [h])
  simpa only [BitVec.add_zero, Nat.add_zero] using this

/-- The scalar's bits are outside the slots and the products' working space. -/
theorem Bits.of_fkeep {base : Addr} {n k : Nat} {s t : State} (hn : n ≤ 57) (hs : Scr s base)
    (h : Bits n base k s.mem) (hk : FKeep base s t) : Bits n base k t.mem := fun q hq => by
  have hn := hs.nowrap
  rw [hk.mem _ (by rw [ofs_off0 base (by simp only [BITS]; omega_arith)]; simp only [BITS]; omega_using [])
    (by rw [ofs_off0 base (by simp only [BITS]; omega_arith)]; simp only [BITS, ACC]; omega_arith)]
  exact h q hq

/-- `0 - x` into slot 10. -/
theorem subNeg_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (ox : Index)
    (hox : ox ≠ 10) (hx : Bnd Mb s.mem base (slot ox.val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (VG.Impl.X448.AArch64.Fast.ops [.sub (slot (10 : Index).val) (slot (19 : Index).val) (slot ox.val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [10] s.mem t.mem ∧
      EV t.mem base = Function.update (EV s.mem base) 10 (EV s.mem base 19 - EV s.mem base ox) :=
  subOp hs hb h19 hx (by decide) (Ne.symm hox) fun _ k b sm e => WP.block_nil ⟨k, b, sm, e⟩

theorem negate_eq (ox : Index) (n : Nat) :
    negate (slot ox.val) n (slot (10 : Index).val) =
      VG.Impl.X448.AArch64.Fast.codeOf ([.sub (slot (10 : Index).val) (slot (19 : Index).val) (slot ox.val)] :
          List Impl.X448.AArch64.Fast.Op) ++
        (([.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (n + 3), .subImm .x .x6 .x6 1] : List Instr) ++
          VG.Impl.Curve448.AArch64.cswap (slot ox.val) (slot (10 : Index).val)) := by
  simp only [negate, List.append_assoc]; rfl

/-- **The negation** of the entry's `x` in slot `ox` for the digit `nib k i - 8`, if negative. -/
theorem negate_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {k j i o : Nat}
    (ox : Index) (hox : ox ≠ 10) {n : Nat} (hn : n ≤ 57) (hj : j < 57) (hi : i < 2 * n)
    (hoi : 8 * j + o = BITS + 4 * i) (ho : o + 3 < 4096) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : Bits n base k s.mem)
    (hx : Bnd Mb s.mem base (slot ox.val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (.block (negate (slot ox.val) o (slot (10 : Index).val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([10] ++ [ox, 10]) s.mem t.mem ∧
      EV t.mem base = opSwap ox 10 (decide (nib k i < 8))
        (Function.update (EV s.mem base) 10 (EV s.mem base 19 - EV s.mem base ox)) := by
  rw [negate_eq ox o, WP.block_append_iff]
  refine WP.mono (block_codeOf (subNeg_ok hs hb ox hox hx h19)) fun t1 ⟨k1, b1, s1, e1⟩ => ?_
  have hs1 := k1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok hs1 hn hj hi hoi ho (by rw [k1.regs.1 _ (by decide)]; exact hc)
    (Bits.of_fkeep hn hs hbits k1)) fun t2 ⟨m2, k2, mem2⟩ => ?_
  have f2 : FKeep base t1 t2 := ⟨k2.mono (by decide), fun x _ _ => by rw [mem2]⟩
  have hs2 := f2.scr hs1
  have b2 : BEnv t2.mem base := fun i => by
    have := b1 i; intro w hw; rw [show t2.mem = t1.mem from mem2]; exact this w hw
  refine WP.mono (VG.Proof.X448.AArch64.Fast.cswapE hs2 b2 ox 10 hox m2) fun t3 ⟨k3, b3, _, _, _, s3, e3⟩ =>
    ⟨k1.trans (f2.trans k3), b3, fun i hi w hw => ?_, ?_⟩
  · have hi' : i ∉ [(10 : Index)] := fun h => hi (List.mem_append_left _ h)
    have hi'' : i ∉ [ox, 10] := fun h => hi (List.mem_append_right _ h)
    rw [s3 i hi'' w hw, show limbs t2.mem base (slot i.val) w = limbs t1.mem base (slot i.val) w by
      rw [mem2], s1 i hi' w hw]
  · rw [e3, show EV t2.mem base = EV t1.mem base by rw [mem2], e1]

end VG.Proof.X448.AArch64.Base

end

end

/-!
# X448 of the base point on AArch64: one step of the comb

Untrusted: everything here is checked by Lean. Step `j` reads both digits,
selects table `j`'s entries, negates each for a negative digit and adds it to
its accumulator: the invariant `StepInv` (as Ed25519's `CombInv`) holds for
`j + 1` after the step if it held for `j`.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib mag)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The entries' slots. -/
def entrySlots : List Index := [6, 7, 8, 9]

theorem slot_entry (i : Index) : i ∈ entrySlots ↔ OX ≤ slot i.val ∧ slot i.val < OX + 512 := by
  have := i.isLt
  simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false, OX, slot, Fin.ext_iff]
  omega_arith

/-- A selection, in the slot environment. -/
theorem selected_env {s t : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {j ao ae : Nat}
    (h : Selected base j ao ae s t) :
    BEnv t.mem base ∧ Same base entrySlots s.mem t.mem ∧
    EV t.mem base 6 = (Impl.X448.baseTable j ao).1 ∧ EV t.mem base 7 = (Impl.X448.baseTable j ao).2 ∧
    EV t.mem base 8 = (Impl.X448.baseTable j ae).1 ∧ EV t.mem base 9 = (Impl.X448.baseTable j ae).2 ∧
    (∀ i ∈ entrySlots, Bnd Mb t.mem base (slot i.val)) := by
  obtain ⟨hv, hf, _⟩ := h
  have hn := hs.nowrap
  -- Words outside the entries' slots are kept.
  obtain keep : ∀ i : Index, i ∉ entrySlots → ∀ w < 8, limbs t.mem base (slot i.val) w = limbs s.mem base (slot i.val) w :=
    fun i hi w hw => by
      have := i.isLt
      obtain hi' := (slot_entry i).not.mp hi
      simp only [OX, slot] at hi'
      exact congrArg BitVec.toNat (hf.word (by simp only [OX, slot]; omega_arith) (by simp only [slot]; omega_arith))
  -- The entries' limbs.
  obtain lv : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, word t.mem base (o + 8 * w) = limb v w) →
      (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) := fun v o h w hw => by
    show (word t.mem base (o + 8 * w)).toNat = _; rw [h w hw]
  obtain l6 := lv _ OX fun w hw => (hv w hw).1
  obtain l8 := lv _ EX fun w hw => (hv w hw).2.1
  obtain l7 := lv _ OY fun w hw => (hv w hw).2.2.1
  obtain l9 := lv _ EY fun w hw => (hv w hw).2.2.2
  obtain fe : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      VG.Proof.X448.AArch64.Weak.F t.mem base o = v := fun v o h => by
    simp only [VG.Proof.X448.AArch64.Weak.F]
    rw [VG.Proof.X448.Wide.valN_congr h, limb_val, VG.Proof.X448.toFe_self]
  obtain bd : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      Bnd Mb t.mem base o := fun v o h w hw => by
    rw [h w hw]; exact Nat.lt_of_lt_of_le (limb_lt v w) (by decide)
  refine ⟨fun i => ?_, keep, fe _ _ l6, fe _ _ l7, fe _ _ l8, fe _ _ l9, ?_⟩
  · by_cases hi : i ∈ entrySlots
    · simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l6 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l7 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l8 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l9 w hw) (by decide)
    · intro w hw; rw [keep i hi w hw]; exact hb i w hw
  · intro i hi
    simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bd _ _ l6
    · exact bd _ _ l7
    · exact bd _ _ l8
    · exact bd _ _ l9

/-! ## The invariant -/

open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.X448 (oddSumZ evenSumZ combG)

/-- The state of a comb of `n` tables before step `j` (of the scalar `k`), from the function's
state after its setup `s₀`. -/
structure StepInv (n : Nat) (s₀ : State) (base : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ n
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  bits : Bits n base k s.mem
  odd : Rep (pt (EV s.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k j) • baseAff)
  even : Rep (pt (EV s.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k j) • baseAff)
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem
  tbl : TblAt s base (s₀.syms combSym)
  keep : ∀ r, r ∉ .x1 :: .x19 :: VG.Proof.X448.AArch64.Fast.fclob → s.gpr r = s₀.gpr r

/-- What every phase after the setup keeps. -/
structure Frame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

/-- What the comb needs before its accumulators are set: the working space, every slot's limbs
below `Ib`, slot 19 zero, the bits of `k` and the tables. -/
structure CombPre (n : Nat) (base : Addr) (k : Nat) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  bits : Bits n base k s.mem
  tbl : TblAt s base (s.syms combSym)

/-! ## One step -/

open VG.Proof.X448 (addPt addPt_rep basePt negAff baseEntry_ok nib_lt mag_lt sdig)

theorem step_eq : VG.Impl.X448.AArch64.Base.stepR =
    .seq (.block digits) (.seq (.block select) (.block (
      negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val) ++
      (addAffine (slot (0 : Index).val) (slot (1 : Index).val) (slot (2 : Index).val)
        (slot (6 : Index).val) (slot (7 : Index).val) ++
      (negate (slot (8 : Index).val) BITS (slot (10 : Index).val) ++
      (addAffine (slot (3 : Index).val) (slot (4 : Index).val) (slot (5 : Index).val)
        (slot (8 : Index).val) (slot (9 : Index).val) ++
      ([.addImm .x .x19 .x19 1, .sub .x .x9 .x19 .x30] : List Instr))))))) := by
  simp only [VG.Impl.X448.AArch64.Base.stepR, List.append_assoc]; rfl

/-- The selected scalar slots outside `entrySlots` are kept by a selection. -/
theorem Selected.outside2 {base : Addr} {j ao ae : Nat} {s t : State} (h : Selected base j ao ae s t) :
    Outside2 base 64 2816 ACC 1152 s.mem t.mem := fun x h1 _ =>
  h.2.1 x (by simp only [OX, slot] at h1 ⊢; omega_arith)

/-- The entry for the digit `n - 8`, negated as `negate` does. -/
theorem entry_eq (e : Spec.X448.Fe × Spec.X448.Fe) (z : Spec.X448.Fe) (hz : z = 0) (n : Nat) :
    (⟨if decide (n < 8) then z - e.1 else e.1, e.2, 1⟩ : Spec.Ed448.Point) =
      basePt (if n < 8 then negAff e else e) := by
  subst hz
  by_cases hn : n < 8
  · simp only [hn, decide_true, ↓reduceIte]; rfl
  · simp only [hn, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl

theorem acc_step (G : ℤ) (S : ℤ) (n j : Nat) :
    (G + S) • baseAff + (((n : ℤ) - 8) * 256 ^ j) • baseAff = (G + (S + ((n : ℤ) - 8) * 256 ^ j)) • baseAff := by
  rw [← add_smul, add_assoc]

/-- The tables survive what keeps the regions and changes only the scalar slots and `ACC`. -/
theorem TblAt.of_outside2 {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : Outside2 base 64 2816 ACC 1152 s.mem t.mem) :
    TblAt t base T :=
  h.of_far hrw fun x hx => hm x (by omega_arith) (by simp only [ACC]; omega_arith)

theorem notin_keep {l : List Reg} (h : ∀ q ∈ l, q ∈ .x1 :: .x19 :: VG.Proof.X448.AArch64.Fast.fclob)
    {r : Reg} (hr : r ∉ .x1 :: .x19 :: VG.Proof.X448.AArch64.Fast.fclob) : r ∉ l := fun e => hr (h r e)

theorem step_ok {n : Nat} (hn : n ≤ 57) {s₀ s : State} {base : Addr} {k j : Nat}
    (h : StepInv n s₀ base k j s) (hj : j < n) (hsy : s.syms = s₀.syms) (h30 : s₀.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa VG.Impl.X448.AArch64.Base.stepR s fun t =>
      (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧ StepInv n s₀ base k (j + 1) t := by
  obtain ⟨_, hs, hb, hz, hc, hbits, hodd, heven, hlr, hout, hrd, hwr, hmem, htbl, hkeep⟩ := h
  obtain no := nib_lt k (2 * j + 1)
  obtain ne := nib_lt k (2 * j)
  rw [step_eq]
  -- The digits.
  refine WP.seq (WP.mono_syms (digits_ok hs hn hj hc hbits) fun t1 ⟨d1, m1⟩ sy1 => ?_)
  obtain hs1 : Scr t1 base := hs.of_keeps d1.keeps (by decide)
  obtain hb1 : BEnv t1.mem base := by rw [m1]; exact hb
  obtain hm1 : Masks (mag (nib k (2 * j + 1))) (mag (nib k (2 * j))) t1 :=
    ⟨d1.oddMask, d1.evenMask, d1.oddZero, d1.evenZero⟩
  obtain hc1 : t1.gpr .x19 = BitVec.ofNat 64 j := by rw [d1.keeps.1 _ (by decide)]; exact hc
  -- The selection.
  obtain tb1 : TblAt t1 base (s₀.syms combSym) :=
    htbl.of_far (by rw [d1.keeps.2.1, d1.keeps.2.2]) fun x _ => by rw [m1]
  refine WP.seq (WP.mono (select_ok hs1 tb1 (by rw [sy1, hsy]) (by omega_arith) hc1 (mag_lt no) (mag_lt ne)
    hm1) fun t2 (h2 : Selected base j _ _ t1 t2) => ?_)
  obtain ⟨b2, s2, v6, v7, v8, v9, bnd2⟩ := selected_env hs1 hb1 h2
  obtain hs2 : Scr t2 base := hs1.of_keeps h2.2.2 (by decide)
  obtain hc2 : t2.gpr .x19 = BitVec.ofNat 64 j := by rw [h2.2.2.1 _ (by decide)]; exact hc1
  obtain bits2 : Bits n base k t2.mem := fun q hq => by
    have hn := hs.nowrap
    rw [h2.2.1 _ (by rw [ofs_off0 base (by simp only [BITS]; omega_arith)]; simp only [OX, BITS, slot]; omega_arith), m1]
    exact hbits q hq
  obtain z2 : ∀ w < 8, limbs t2.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s2 19 (by decide) w hw]; rw [m1]; exact hz w hw
  obtain e1 : EV t1.mem base = EV s.mem base := by rw [m1]
  -- The odd digit's entry, negated, and added to `A`.
  rw [WP.block_append_iff]
  refine WP.mono (negate_ok hs2 b2 (k := k) (i := 2 * j + 1) (o := BITS + 4) 6 (by decide) hn (by omega_arith) (by omega_arith)
    (by simp only [BITS]; omega_arith) (by simp only [BITS]; omega_arith) hc2 bits2 (bnd2 6 (by decide))
    (zero_env z2).2) fun t3 ⟨k3, b3, s3, e3⟩ => ?_
  obtain hs3 := k3.scr hs2
  obtain z3 : ∀ w < 8, limbs t3.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s3 19 (by decide) w hw]; exact z2 w hw
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 0 1 2 6 7 (by decide) (by decide) (by decide) hs3 b3 (zero_env z3).2
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun t4 ⟨k4, b4, s4, _, _, _, e4⟩ => ?_
  obtain hs4 := k4.scr hs3
  obtain z4 : ∀ w < 8, limbs t4.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s4 19 (by decide) w hw]; exact z3 w hw
  obtain hc4 : t4.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k4.regs.1 .x19 (by decide), k3.regs.1 .x19 (by decide)]; exact hc2
  -- The even digit's entry, negated, and added to `B`.
  rw [WP.block_append_iff]
  refine WP.mono (negate_ok hs4 b4 (k := k) (i := 2 * j) (o := BITS) 8 (by decide) hn (by omega_arith) (by omega_arith)
    (by omega_arith) (by simp only [BITS]; omega_arith) hc4
    (Bits.of_fkeep hn hs3 (Bits.of_fkeep hn hs2 bits2 k3) k4)
    (s4.bnd (by decide) (s3.bnd (by decide) (bnd2 8 (by decide)))) (zero_env z4).2)
    fun t5 ⟨k5, b5, s5, e5⟩ => ?_
  obtain hs5 := k5.scr hs4
  obtain z5 : ∀ w < 8, limbs t5.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s5 19 (by decide) w hw]; exact z4 w hw
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 3 4 5 8 9 (by decide) (by decide) (by decide) hs5 b5 (zero_env z5).2
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)) (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun t6 ⟨k6, b6, s6, _, _, _, e6⟩ => ?_
  obtain hs6 := k6.scr hs5
  -- The counter.
  obtain hc6 : t6.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k6.regs.1 .x19 (by decide), k5.regs.1 .x19 (by decide)]; exact hc4
  obtain h6 : t6.gpr .x30 = BitVec.ofNat 64 n := by
    rw [k6.regs.1 .x30 (by decide), k5.regs.1 .x30 (by decide), k4.regs.1 .x30 (by decide),
      k3.regs.1 .x30 (by decide), h2.2.2.1 .x30 (by decide), d1.keeps.1 .x30 (by decide), hkeep .x30 (by decide), h30]
  refine WP.mono (nextR_ok t6 hn hj hc6 h6) fun t7 ⟨c7, n7, k7, m7⟩ => ⟨n7, ?_⟩
  obtain hs7 : Scr t7 base := hs6.of_keeps k7 (by decide)
  obtain z6 : ∀ w < 8, limbs t6.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s6 19 (by decide) w hw]; exact z5 w hw
  -- Values of the slots along the way.
  obtain e2s : ∀ i : Index, i ∉ entrySlots → EV t2.mem base i = EV s.mem base i := fun i hi => by
    rw [Same.env s2 hi, e1]
  obtain z2v : EV t2.mem base 19 = 0 := (zero_env z2).1
  obtain t3o : ∀ i : Index, i ≠ 6 → i ≠ 10 → EV t3.mem base i = EV t2.mem base i := fun i h6 h10 => by
    rw [e3]; simp only [opSwap, Function.update_apply, h6, h10, ite_false]
  obtain t36 : EV t3.mem base 6 =
      if decide (nib k (2 * j + 1) < 8) then EV t2.mem base 19 - EV t2.mem base 6 else EV t2.mem base 6 := by
    rw [e3]; simp only [opSwap, Function.update_apply, show (6 : Index) ≠ 10 by decide, ite_false, ite_true]
  obtain t5o : ∀ i : Index, i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t4.mem base i := fun i h8 h10 => by
    rw [e5]; simp only [opSwap, Function.update_apply, h8, h10, ite_false]
  obtain t58 : EV t5.mem base 8 =
      if decide (nib k (2 * j) < 8) then EV t4.mem base 19 - EV t4.mem base 8 else EV t4.mem base 8 := by
    rw [e5]; simp only [opSwap, Function.update_apply, show (8 : Index) ≠ 10 by decide, ite_false, ite_true]
  obtain t4s : ∀ i : Index, i ∉ temps ++ [2, 0, 1] → i ∉ [10] ++ [6, 10] →
      EV t4.mem base i = EV t2.mem base i := fun i h4 h3 => by
    rw [Same.env s4 h4, Same.env s3 h3]
  -- The odd accumulator.
  obtain pA : pt (EV t4.mem base) 0 1 2 = addPt (pt (EV s.mem base) 0 1 2)
      (basePt (if nib k (2 * j + 1) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j + 1))))
        else Impl.X448.baseTable j (mag (nib k (2 * j + 1))))) := by
    rw [e4, affEnv_A, t3o 0 (by decide) (by decide), t3o 1 (by decide) (by decide),
      t3o 2 (by decide) (by decide), t36, t3o 7 (by decide) (by decide), t3o 19 (by decide) (by decide),
      z2v, v6, v7, e2s 0 (by decide), e2s 1 (by decide), e2s 2 (by decide), affPt_eq,
      entry_eq _ 0 rfl]
    rfl
  obtain pB : pt (EV t6.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5)
      (basePt (if nib k (2 * j) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j))))
        else Impl.X448.baseTable j (mag (nib k (2 * j))))) := by
    rw [e6, affEnv_B, t5o 3 (by decide) (by decide), t5o 4 (by decide) (by decide),
      t5o 5 (by decide) (by decide), t58, t5o 9 (by decide) (by decide), t5o 19 (by decide) (by decide),
      t4s 3 (by decide) (by decide), t4s 4 (by decide) (by decide), t4s 5 (by decide) (by decide),
      t4s 8 (by decide) (by decide), t4s 9 (by decide) (by decide), t4s 19 (by decide) (by decide),
      z2v, v8, v9, e2s 3 (by decide), e2s 4 (by decide), e2s 5 (by decide), affPt_eq,
      entry_eq _ 0 rfl]
    rfl
  obtain p7A : pt (EV t7.mem base) 0 1 2 = pt (EV t4.mem base) 0 1 2 := by
    simp only [pt, m7]
    rw [Same.env s6 (i := 0) (by decide), Same.env s5 (i := 0) (by decide),
      Same.env s6 (i := 1) (by decide), Same.env s5 (i := 1) (by decide),
      Same.env s6 (i := 2) (by decide), Same.env s5 (i := 2) (by decide)]
  obtain p7B : pt (EV t7.mem base) 3 4 5 = pt (EV t6.mem base) 3 4 5 := by simp only [pt, m7]
  refine ⟨by omega_arith, hs7, by rw [m7]; exact b6, by rw [m7]; exact z6, c7,
    by rw [m7]; exact Bits.of_fkeep hn hs5 (Bits.of_fkeep hn hs4 (Bits.of_fkeep hn hs3 (Bits.of_fkeep hn hs2 bits2 k3) k4) k5) k6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p7A, pA]
    have := addPt_rep hodd (baseEntry_ok j (nib k (2 * j + 1)) (by omega_arith) no)
    rw [acc_step] at this
    exact this
  · rw [p7B, pB]
    have := addPt_rep heven (baseEntry_ok j (nib k (2 * j)) (by omega_arith) ne)
    rw [acc_step] at this
    exact this
  · rw [k7.1 .x30 (by decide), k6.regs.1 .x30 (by decide), k5.regs.1 .x30 (by decide),
      k4.regs.1 .x30 (by decide), k3.regs.1 .x30 (by decide), h2.2.2.1 .x30 (by decide),
      d1.keeps.1 .x30 (by decide)]; exact hlr
  · rw [k7.1 .x20 (by decide), k6.regs.1 .x20 (by decide), k5.regs.1 .x20 (by decide),
      k4.regs.1 .x20 (by decide), k3.regs.1 .x20 (by decide), h2.2.2.1 .x20 (by decide),
      d1.keeps.1 .x20 (by decide)]; exact hout
  · rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k4.regs.2.1, k3.regs.2.1, h2.2.2.2.1, d1.keeps.2.1]; exact hrd
  · rw [k7.2.2, k6.regs.2.2, k5.regs.2.2, k4.regs.2.2, k3.regs.2.2, h2.2.2.2.2, d1.keeps.2.2]; exact hwr
  · rw [m7]
    refine Outside2.trans hmem ?_
    rw [← m1]
    exact (((h2.outside2.trans k3.mem).trans k4.mem).trans k5.mem).trans k6.mem
  · refine htbl.of_outside2 (by rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k4.regs.2.1, k3.regs.2.1,
      h2.2.2.2.1, d1.keeps.2.1, k7.2.2, k6.regs.2.2, k5.regs.2.2, k4.regs.2.2, k3.regs.2.2,
      h2.2.2.2.2, d1.keeps.2.2]) ?_
    rw [m7, ← m1]
    exact (((h2.outside2.trans k3.mem).trans k4.mem).trans k5.mem).trans k6.mem
  · intro r hr
    rw [k7.1 r (notin_keep (by decide) hr), k6.regs.1 r (notin_keep (by decide) hr),
      k5.regs.1 r (notin_keep (by decide) hr), k4.regs.1 r (notin_keep (by decide) hr),
      k3.regs.1 r (notin_keep (by decide) hr), h2.2.2.1 r (notin_keep (by decide) hr),
      d1.keeps.1 r (notin_keep (by decide) hr)]
    exact hkeep r hr

/-! ## The steps -/

theorem loop_ok {n : Nat} (hn : n ≤ 57) {s₀ : State} {base : Addr} {k : Nat}
    (h30 : s₀.gpr .x30 = BitVec.ofNat 64 n) :
    ∀ m, ∀ s, 1 ≤ m → m ≤ n → StepInv n s₀ base k (n - m) s → s.syms = s₀.syms →
      WP isa (.loop VG.Impl.X448.AArch64.Base.stepR (.nonzero .x .x9)) s fun t =>
        StepInv n s₀ base k n t := by
  intro m s h1 h2 hi hsy
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.Base.stepR) (c := .nonzero .x .x9)
    (Q := fun t => StepInv n s₀ base k n t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ StepInv n s₀ base k (n - m) s ∧ s.syms = s₀.syms) ?_ m s
    ⟨h1, h2, hi, hsy⟩
  intro m s ⟨h1, h2, hi, hsy⟩
  refine WP.mono_syms (step_ok hn hi (by omega_arith) hsy h30) fun t ⟨hz, ht⟩ tsy => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    rw [show n - 1 + 1 = n by omega_arith] at ht ⊢
    exact .inl ⟨by simp, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega_arith)), m - 1, by omega_arith, by omega_arith, by omega_arith, ?_,
      tsy.trans hsy⟩
    rw [show n - (m - 1) = n - m + 1 by omega_arith]
    exact ht

end VG.Proof.X448.AArch64.Base
