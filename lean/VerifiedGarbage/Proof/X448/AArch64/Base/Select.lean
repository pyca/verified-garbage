import VerifiedGarbage.Proof.X448.AArch64.Base.Digit
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/-!
# X448 of the base point on AArch64: the constant-time selection

Untrusted: everything here is checked by Lean. As Ed25519's comb
(`Proof/Ed25519/AArch64/CombSelect.lean`): with `oddReg m` (`evenReg m`) all
ones exactly for `m` the odd (even) digit's magnitude, and `x5` (`x0`) the bit
of a zero magnitude, `selectWord` builds every candidate's limb from
immediates once, ANDs it with both digits' masks and ORs it into `x1` and `x2`,
so only each digit's candidate survives, and stores them. Nothing here
unfolds a table: each lemma holds for any immediate.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside2 ofs store_ok word_write writeW_outside)
open VG.Proof.Curve448.AArch64 (mask)

private theorem odd_regs : ∀ m < 9, oddReg m ∉ [Reg.x6, .x7, .x1, .x2] := by decide
private theorem even_regs : ∀ m < 9, evenReg m ∉ [Reg.x6, .x7, .x1, .x2] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

/-- One candidate's limb: built in `x6`, masked into `x1` (odd) and `x2` (even). -/
def candCode (v : Spec.X448.Fe) (m w : Nat) : List Instr :=
  const64 .x6 (limb v w) ++
    [.logic .and .x .x7 .x6 (oddReg m), .logic .orr .x .x1 .x1 .x7,
      .logic .and .x .x7 .x6 (evenReg m), .logic .orr .x .x2 .x2 .x7]

theorem cand_ok (s : State) (v : Spec.X448.Fe) {m : Nat} (hm : m < 9) (w : Nat) :
    WP isa (.block (candCode v m w)) s fun t =>
      t.gpr .x1 = s.gpr .x1 ||| (limb v w &&& s.gpr (oddReg m)) ∧
      t.gpr .x2 = s.gpr .x2 ||| (limb v w &&& s.gpr (evenReg m)) ∧
      Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  have ho := odd_regs m hm
  have he := even_regs m hm
  have ho6 := ne_of_not_mem ho (r' := .x6) (by decide)
  have he6 := ne_of_not_mem he (r' := .x6) (by decide)
  have he7 := ne_of_not_mem he (r' := .x7) (by decide)
  have he1 := ne_of_not_mem he (r' := .x1) (by decide)
  rw [candCode, WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x6 (limb v w)) fun a ⟨a6, ka, ea⟩ => ?_
  have am : a.gpr (oddReg m) = s.gpr (oddReg m) := ka _ ho6
  have ae : a.gpr (evenReg m) = s.gpr (evenReg m) := ka _ he6
  have a1 : a.gpr .x1 = s.gpr .x1 := ka _ (by decide)
  have a2 : a.gpr .x2 = s.gpr .x2 := ka _ (by decide)
  have amem : a.mem = s.mem := by rw [ea]
  have ard : a.rd = s.rd := by rw [ea]
  have awr : a.wr = s.wr := by rw [ea]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, RegUpd.gpr_write,
    BitVec.setWidth_eq, he7, he1, ite_true, ite_false, reduceCtorEq, a6, am, ae, a1, a2,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, ard, awr⟩, amem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  exact ka _ hr.1

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

private theorem odd_regs9 : ∀ m < 9, oddReg m ∉ [Reg.x9, .x6, .x7, .x1, .x2] := by decide
private theorem even_regs9 : ∀ m < 9, evenReg m ∉ [Reg.x9, .x6, .x7, .x1, .x2] := by decide

theorem Masks.of_keeps {ao ae : Nat} {rs : List Reg} {s t : State} (h : Masks ao ae s)
    (k : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ [Reg.x9, .x6, .x7, .x1, .x2] := by simp) :
    Masks ao ae t := by
  have nm : ∀ r, r ∉ [Reg.x9, .x6, .x7, .x1, .x2] → r ∉ rs := fun r hr hm => hr (hrs r hm)
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, ?_, ?_⟩
  · rw [k.1 _ (nm _ (odd_regs9 j (by omega)))]; exact h.1 j h1 h8
  · rw [k.1 _ (nm _ (even_regs9 j (by omega)))]; exact h.2.1 j h1 h8
  · rw [k.1 _ (nm _ (by decide))]; exact h.2.2.1
  · rw [k.1 _ (nm _ (by decide))]; exact h.2.2.2

theorem cands_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s)
    (vs : List Spec.X448.Fe) (w n : Nat) (hn : n ≤ 8)
    (h0 : s.gpr .x1 = selWord vs ao 0 w ∧ s.gpr .x2 = selWord vs ae 0 w) :
    WP isa (.block ((List.range n).flatMap fun m => candCode (vs.getD (m + 1) 0) (m + 1) w)) s
      fun t => t.gpr .x1 = selWord vs ao n w ∧ t.gpr .x2 = selWord vs ae n w ∧
        Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨h0.1, h0.2, ⟨fun _ _ => rfl, rfl, rfl⟩, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t1, t2, kt, mt⟩ => ?_
    have tm := hm.of_keeps kt
    refine WP.mono (cand_ok t _ (by omega : n + 1 < 9) w) fun u ⟨u1, u2, ku, mu⟩ =>
      ⟨?_, ?_, kt.trans ku, mu.trans mt⟩
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

theorem selectWord_eq (one : Bool) (vs : List Spec.X448.Fe) (o e w : Nat) :
    selectWord one vs o e w = startCode one w ++
      ((List.range 8).flatMap fun m => candCode (vs.getD (m + 1) 0) (m + 1) w) ++
      [st .x1 (o + 8 * w), st .x2 (e + 8 * w)] := rfl

theorem word_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hm : Masks ao ae s)
    (one : Bool) (vs : List Spec.X448.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hb : o + 64 ≤ 8192) (hbe : e + 64 ≤ 8192)
    (w : Nat) (hw : w < 8) :
    WP isa (.block (selectWord one vs o e w)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 8 * w)) (selWord vs ao 8 w)).writeW (off base (e + 8 * w))
        (selWord vs ae 8 w) ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  rw [selectWord_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (start_ok s hm one vs h0 w hw) fun a ⟨a1, a2, ka, ma⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cands_ok a (hm.of_keeps ka) vs w 8 (le_refl _) ⟨a1, a2⟩)
    fun b ⟨b1, b2, kb, mb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  rw [show ([st .x1 (o + 8 * w), st .x2 (e + 8 * w)] : List Instr) =
    [st .x1 (o + 8 * w)] ++ [st .x2 (e + 8 * w)] from rfl, WP.block_append_iff]
  refine WP.mono (store_ok hsb (by omega) (by omega) .x1) fun c ⟨mc, kc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (store_ok hsc (by omega) (by omega) .x2) fun t ⟨mt, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, mc, kc.1 _ (by decide), b1, b2, mb, ma]
  · exact ((ka.trans kb).trans (kc.mono (by simp))).trans (kt.mono (by simp))

theorem fieldPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat}
    (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X448.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 64 ≤ e ∨ e + 64 ≤ o)
    (hb : o + 64 ≤ 8192) (hbe : e + 64 ≤ 8192) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord one vs o e w)) s fun t =>
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
    refine WP.mono (word_ok ht (hm.of_keeps kt) one vs h0 ho he hb hbe n (by omega))
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

theorem limb_valN (v : Spec.X448.Fe) : ∀ n, VG.Proof.X448.Wide.valN (fun i => (limb v i).toNat) n =
    v.val % VG.Proof.X448.Wide.radix ^ n
  | 0 => by simp [VG.Proof.X448.Wide.valN, Nat.mod_one]
  | n + 1 => by
    rw [VG.Proof.X448.Wide.valN_succ, limb_valN v n, Nat.pow_succ, Nat.mod_mul]
    congr 2
    simp only [limb, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
      show 2 ^ (56 * n) = VG.Proof.X448.Wide.radix ^ n by rw [Nat.pow_mul]; rfl]
    rfl

theorem limb_val (v : Spec.X448.Fe) : VG.Proof.X448.Wide.valN (fun i => (limb v i).toNat) 8 = v.val := by
  rw [limb_valN]
  refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt ?_)
  rw [show VG.Proof.X448.Wide.radix ^ 8 = VG.Proof.X448.Wide.full from rfl, VG.Proof.X448.Wide.full_eq]
  omega

theorem limb_lt (v : Spec.X448.Fe) (w : Nat) : (limb v w).toNat < 2 ^ 56 := by
  simp only [limb, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) :
    (((List.range 9).map (Impl.X448.baseTable j)).map f).getD a 0 = f (Impl.X448.baseTable j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

/-- The entries' slots, 6–9, are the 512 bytes at `OX`. -/
theorem entries_span : OY = OX + 128 ∧ EX = OX + 256 ∧ EY = OX + 384 ∧ OX = 832 := by decide

/-- **Table `j`'s entries** for both digits, `|d| = ao` and `ae`, to slots 6–9, limb by limb. -/
theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (j : Nat) :
    WP isa (.block (select j)) s fun t =>
      (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
        word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
        word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
        word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
      VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  rw [select, WP.block_append_iff]
  refine WP.mono (fieldPrefix_ok hs hm false _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := OX) (e := EX) (by decide) (by decide) (by decide) (by decide) (by decide) 8 (le_refl _))
    fun b ⟨bv, bf, kb⟩ => ?_
  have hsb : Scr b base := hs.of_keeps kb (by decide)
  refine WP.mono (fieldPrefix_ok hsb (hm.of_keeps kb) true _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := OY) (e := EY) (by decide) (by decide) (by decide) (by decide) (by decide) 8 (le_refl _))
    fun t ⟨tv, tf, kt⟩ => ⟨fun w hw => ?_, ?_, kb.trans kt⟩
  · obtain ⟨b1, b2⟩ := bv w hw
    obtain ⟨t1, t2⟩ := tv w hw
    have sel : ∀ (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) (a : Nat), a < 9 →
        selWord (((List.range 9).map (Impl.X448.baseTable j)).map f) a 8 w =
          limb (f (Impl.X448.baseTable j a)) w := fun f a ha => by
      unfold selWord; rw [ite_eq_left (by omega), entries_getD j a ha]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tf.word (by simp only [OX, OY, slot]; omega) (by simp only [OX, EY, slot]; omega)
        (by simp only [OX, slot]; omega), b1, sel _ _ hao]
    · rw [tf.word (by simp only [EX, OY, slot]; omega) (by simp only [EX, EY, slot]; omega)
        (by simp only [EX, slot]; omega), b2, sel _ _ hae]
    · rw [t1, sel _ _ hao]
    · rw [t2, sel _ _ hae]
  · intro x hx
    rw [tf x (by simp only [OX, OY, slot] at hx ⊢; omega) (by simp only [OX, EY, slot] at hx ⊢; omega),
      bf x (by simp only [OX, slot] at hx ⊢; omega) (by simp only [OX, EX, slot] at hx ⊢; omega)]

/-- What a selection leaves: table `j`'s entries for both digits in slots 6–9. -/
def Selected (base : Addr) (j ao ae : Nat) (s t : State) : Prop :=
  (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
    word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
    word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
    word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
  VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x9, .x6, .x7, .x1, .x2] s t

theorem dispatch_ok (s : State) {j k : Nat} (hj : j < 56) (hk : k < 56)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x9 .x19 k]) s fun t =>
      (t.gpr .x9 == 0) = decide (j = k) ∧ Keeps [.x9] s t ∧ t.mem = s.mem := by
  have hz : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show k < 4096 by omega, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, hz,
    Option.some.injEq, exists_eq_left']
  exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

theorem selectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 56) {s : State} {base : Addr}
    (hs : Scr s base) {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks ao ae s)
    {j : Nat} (hj : j ∈ ks) (hj56 : j < 56) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (selectFrom ks) s (Selected base j ao ae s) := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 56 := hks k (by simp)
    rw [selectFrom]
    refine WP.seq (WP.mono (dispatch_ok s hj56 hk hc) fun t ⟨tz, kt, mt⟩ => ?_)
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have hm' : Masks ao ae t := hm.of_keeps kt
    refine WP.ite (decide (j = k)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, tz])
      (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (select_ok ht hao hae hm' j) fun u ⟨uv, uf, ku⟩ =>
        ⟨uv, by rw [← mt]; exact uf, (kt.mono (by simp)).trans (ku.mono (by simp))⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ht hm' hj'
        (by rw [kt.1 _ (by decide)]; exact hc)) fun u ⟨uv, uf, ku⟩ =>
        ⟨uv, by rw [← mt]; exact uf, (kt.mono (by simp)).trans ku⟩

end VG.Proof.X448.AArch64.Base
