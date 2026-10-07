import VerifiedGarbage.Proof.X448.AArch64.Base.Digit
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X448.AArch64.Base.Comb

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
    exact h.far _ (by omega)⟩

/-- The tables, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem CombHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : CombHeld s wr)
    (hrd : (⟨s.syms combSym, 8 * combWords.length⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : TblAt s base (s.syms combSym) := by
  obtain ⟨held, fit, dj⟩ := h
  rw [combWords_length] at held fit dj hrd
  have hc : Region.Contains ⟨s.syms combSym, 8 * (57 * 128)⟩ (s.syms combSym) (8 * (57 * 128)) := by
    have := Offset.contains_base (s.syms combSym) (d := 0) (n := 8 * (57 * 128)) (k := 8 * (57 * 128))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨_, hrd, hc⟩, fun i hi => ?_, fun i hi => ?_⟩
  · refine Nat.le_of_not_lt fun hlt => dj _ hsc _
      (Offset.contains_base _ (d := i) (n := 1) (k := 8 * (57 * 128)) (by omega) (by omega)) ?_
    simp only [Region.Contains]; simp only [ofs] at hlt; omega
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
  · simp only [h, ↓reduceIte, show a ≤ n + 1 by omega, show ¬ a = n + 1 by omega, decide_false,
      mask, Bool.false_eq_true]
    exact or_and_zero _ _
  · by_cases he : a = n + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, mask, BitVec.and_allOnes]
      exact BitVec.zero_or
    · simp only [h, he, ↓reduceIte, show ¬ a ≤ n + 1 by omega, decide_false, mask,
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
  · rw [k.1 _ (nm _ (odd_regs9 j (by omega)))]; exact h.1 j h1 h8
  · rw [k.1 _ (nm _ (even_regs9 j (by omega)))]; exact h.2.1 j h1 h8
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
    refine WP.mono (ih (by omega)) fun t ⟨t1, t2, kt, mt⟩ => ?_
    have tm := hm.of_keeps kt
    obtain ⟨hr, hv⟩ := ht.of_keeps kt mt n (by omega)
    refine WP.mono (cand_ok t (by omega : n + 1 < 9) ⟨by omega, by omega⟩ hr hv)
      fun u ⟨u1, u2, ku, mu⟩ => ⟨?_, ?_, kt.trans ku, mu.trans mt⟩
    · rw [u1, t1, tm.1 (n + 1) (by omega) (by omega), sel_step]
    · rw [u2, t2, tm.2.1 (n + 1) (by omega) (by omega), sel_step]

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
    · simp [ha, show ¬ a ≤ 0 by omega]
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
  refine WP.mono (store_ok hsb (by omega) (by omega) .x1) fun c ⟨mc, kc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (store_ok hsc (by omega) (by omega) .x2) fun t ⟨mt, kt⟩ => ⟨?_, ?_⟩
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
    exact Mem.read_congr fun b hb' => hm _ (by have := hf m hm' b hb'; omega)
      (by have := hf m hm' b hb'; omega)

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
    refine WP.mono (ih (by omega)) fun t ⟨tv, tf, kt⟩ => ?_
    have ht : Scr t base := hs.of_keeps kt (by decide)
    refine WP.mono (word_ok ht (hm.of_keeps kt) one vs h0 ho he hb hbe n (by omega)
      ((hc.of_outside2 kt hb hbe tf) n (by omega)).1)
      fun u ⟨um, ku⟩ => ⟨fun w hw => ?_, ?_, kt.trans ku⟩
    · rw [um, VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega)]
      by_cases hwn : w = n
      · subst hwn
        simp only [↓reduceIte, show o + 8 * w ≠ e + 8 * w by omega]
        exact ⟨trivial, trivial⟩
      · simp only [show o + 8 * w ≠ e + 8 * n by omega, show o + 8 * w ≠ o + 8 * n by omega,
          show e + 8 * w ≠ e + 8 * n by omega, show e + 8 * w ≠ o + 8 * n by omega, ↓reduceIte]
        exact tv w (by omega)
    · rw [um]
      refine fun x h1 h2 => ?_
      rw [show ((t.mem.writeW (off base (o + 8 * n)) (selWord vs ao 8 n)).writeW (off base (e + 8 * n))
          (selWord vs ae 8 n)) x = t.mem x from ?_]
      · exact tf x h1 h2
      · rw [VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega),
          VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega)]

/-! ## The selected field's value -/

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) :
    (((List.range 9).map (Impl.X448.baseTable j)).map f).getD a 0 = f (Impl.X448.baseTable j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

/-- The entries' slots, 6–9, are the 512 bytes at `OX`. -/
theorem entries_span : OY = OX + 128 ∧ EX = OX + 256 ∧ EY = OX + 384 ∧ OX = 832 := by decide

/-- `x9` = table `j`'s address, from the static's and `x19 = j`. -/
theorem tblAddr_ok (s : State) {T : Addr} (hT : s.syms combSym = T) {j : Nat} (hj : j < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block tblAddr) s fun t =>
      t.gpr .x9 = T + BitVec.ofNat 64 (1024 * j) ∧ Keeps [.x9, .x8] s t ∧ t.mem = s.mem := by
  have hsh : BitVec.ofNat 64 j <<< 10 = BitVec.ofNat 64 (1024 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 1024 * j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show j * 2 ^ 10 < 2 ^ 64 by omega)]
    omega
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
    omega
  refine ⟨fun m hm => ?_, fun m hm b hb => ?_⟩
  · have := (coordOff_le one)
    have hi : 128 * j + coordOff one / 8 + 8 * m + w < 57 * 128 := by omega
    have a0 := addr m hm 0 (by decide)
    rw [BitVec.add_zero, Nat.add_zero] at a0
    rw [a0]
    refine ⟨VG.CallLay.inRegions_sub h.rd (by omega) (by decide), ?_⟩
    rw [h.val _ hi, combWord, entries_getD j (m + 1) (by omega)]
    have e1 : (128 * j + coordOff one / 8 + 8 * m + w) / 128 = j := by omega
    have e2 : (128 * j + coordOff one / 8 + 8 * m + w) % 64 / 8 + 1 = m + 1 := by
      cases one <;> simp only [coordOff, Bool.false_eq_true, ↓reduceIte] <;> omega
    have e3 : (128 * j + coordOff one / 8 + 8 * m + w) % 8 = w := by
      cases one <;> simp only [coordOff, Bool.false_eq_true, ↓reduceIte] <;> omega
    simp only [e1, e2, e3]
    cases one
    · simp only [coordOff, Bool.false_eq_true, ↓reduceIte, show (128 * j + 0 / 8 + 8 * m + w) % 128 < 64 by omega]
    · simp only [coordOff, ↓reduceIte, show ¬ (128 * j + 512 / 8 + 8 * m + w) % 128 < 64 by omega]
  · rw [addr m hm b hb]
    have := (coordOff_le one)
    exact h.far _ (by omega)

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
      unfold selWord; rw [ite_eq_left (by omega), entries_getD j a ha]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tf.word (by simp only [OX, OY, slot]; omega) (by simp only [OX, EY, slot]; omega)
        (by simp only [OX, slot]; omega), b1, sel _ _ hao]; rfl
    · rw [tf.word (by simp only [EX, OY, slot]; omega) (by simp only [EX, EY, slot]; omega)
        (by simp only [EX, slot]; omega), b2, sel _ _ hae]; rfl
    · rw [t1, sel _ _ hao]; rfl
    · rw [t2, sel _ _ hae]; rfl
  · intro x hx
    rw [tf x (by simp only [OX, OY, slot] at hx ⊢; omega) (by simp only [OX, EY, slot] at hx ⊢; omega),
      bf x (by simp only [OX, slot] at hx ⊢; omega) (by simp only [OX, EX, slot] at hx ⊢; omega), ma]

/-- What a selection leaves: table `j`'s entries for both digits in slots 6–9. -/
def Selected (base : Addr) (j ao ae : Nat) (s t : State) : Prop :=
  (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
    word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
    word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
    word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
  VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x9, .x8, .x6, .x7, .x1, .x2] s t

end VG.Proof.X448.AArch64.Base
