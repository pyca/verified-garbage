import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Ed25519.AArch64.CombTbl
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The comb's constant-time selection, for two digits at once

With `oddReg k` (`evenReg k`) all ones exactly for `k` the odd (even) digit's
magnitude, and `x22` (`x8`) the bit of a zero magnitude, `selectWord` builds
every candidate's word once, ANDs it with both digits' masks and ORs it into
`x4` and `x5`, so only each digit's candidate survives, and stores them. The
candidates are loaded from the tables at `T` (`TblAt`): readable, beyond the
working space, word `i` the static's `combWord i`. Nothing here unfolds a
table: each lemma holds for any words.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 VG.Proof.X25519
open Word64

private theorem odd_regs : ∀ k < 9, oddReg k ∉ [Reg.x9, .x2, .x4, .x5] := by decide
private theorem even_regs : ∀ k < 9, evenReg k ∉ [Reg.x9, .x2, .x4, .x5] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

/-! ## The tables -/

/-- The comb's tables at `T`: readable, beyond the working space at `base`, word `i` the
static's (`combWord i`). -/
structure TblAt (s : State) (base T : Addr) : Prop where
  rd : InRegions (s.rd ++ s.wr) T (8 * (32 * 96))
  far : ∀ i < 8 * (32 * 96), 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 32 * 96, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWord i

theorem tbl_add (T : Addr) (a b : Nat) :
    T + BitVec.ofNat 64 a + BitVec.ofNat 64 b = T + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The tables survive what keeps the regions and the memory beyond the working space. -/
theorem TblAt.of_far {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    TblAt t base T :=
  ⟨hrw ▸ h.rd, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [tbl_add T _ _]
    exact h.far _ (by omega)⟩

/-- The tables, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem CombHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : CombHeld s wr)
    (hrd : (⟨s.syms combSym, 8 * combWords.length⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : TblAt s base (s.syms combSym) := by
  obtain ⟨held, fit, dj⟩ := h
  rw [combWords_length] at held fit dj hrd
  have hc : Region.Contains ⟨s.syms combSym, 8 * (32 * 96)⟩ (s.syms combSym) (8 * (32 * 96)) := by
    have := Offset.contains_base (s.syms combSym) (d := 0) (n := 8 * (32 * 96)) (k := 8 * (32 * 96))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨_, hrd, hc⟩, fun i hi => ?_, fun i hi => ?_⟩
  · refine Nat.le_of_not_lt fun hlt => dj _ hsc _
      (Offset.contains_base _ (d := i) (n := 1) (k := 8 * (32 * 96)) (by omega) (by omega)) ?_
    simp only [Region.Contains]; simp only [ofs] at hlt; omega
  · rw [← combWords_getD hi, ← held i hi]

/-! ## One candidate -/

/-- Load the word at `x9 + d` into `x2`, mask it with `m` and OR it into `a`. -/
theorem half_ok (s : State) {v : BitVec 64} {d : Nat} {m a : Reg} (hm2 : m ≠ .x2) (ha2 : a ≠ .x2)
    (hd : d % 8 = 0 ∧ d < 32768) (hr : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 d) 8)
    (hv : s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 d) 64 = v) :
    WP isa (.block [.ldr .x .x2 .x9 d, .logic .and .x .x2 .x2 m, .logic .orr .x a a .x2]) s
      fun t => t.gpr a = s.gpr a ||| (v &&& s.gpr m) ∧ Keeps [.x2, a] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec_ldr_x hd hr, hv]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, hm2, ha2, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Word `w` of a candidate, at `x9 + d`, into both digits' selections. -/
theorem cand_ok (s : State) {v : BitVec 64} {k d : Nat} (hk : k < 9) (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 d) 8)
    (hv : s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 d) 64 = v) :
    WP isa (.block (selectCand d k)) s fun t =>
      t.gpr .x4 = s.gpr .x4 ||| (v &&& s.gpr (oddReg k)) ∧
      t.gpr .x5 = s.gpr .x5 ||| (v &&& s.gpr (evenReg k)) ∧
      Keeps [.x2, .x4, .x5] s t := by
  have ho := odd_regs k hk
  have he := even_regs k hk
  rw [show selectCand d k = [.ldr .x .x2 .x9 d, .logic .and .x .x2 .x2 (oddReg k), .logic .orr .x .x4 .x4 .x2] ++
    [.ldr .x .x2 .x9 d, .logic .and .x .x2 .x2 (evenReg k), .logic .orr .x .x5 .x5 .x2] from rfl,
    WP.block_append_iff]
  refine WP.mono (half_ok s (ne_of_not_mem ho (by decide)) (by decide) hd hr hv) fun a ⟨a4, ka⟩ => ?_
  have a9 : a.gpr .x9 = s.gpr .x9 := ka.gpr _ (by decide)
  refine WP.mono (half_ok a (v := v) (ne_of_not_mem he (by decide)) (by decide) hd
    (by rw [ka.rd, ka.wr, a9]; exact hr) (by rw [ka.mem, a9]; exact hv)) fun t ⟨t5, kt⟩ => ?_
  have hea : a.gpr (evenReg k) = s.gpr (evenReg k) := ka.gpr _ fun hm => he (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h <;> simp [h])
  refine ⟨?_, ?_, (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  · rw [kt.gpr _ (by decide), a4]
  · rw [t5, hea, ka.gpr _ (by decide)]

/-- The words of `vs[a]` after the candidates `k ≤ n`, zero if `a > n`. -/
def selWord (vs : List Spec.X25519.Fe) (a n w : Nat) : BitVec 64 :=
  if a ≤ n then feWord (vs.getD a 0) w else 0

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp

theorem sel_step (vs : List Spec.X25519.Fe) (a n w : Nat) :
    selWord vs a n w ||| (feWord (vs.getD (n + 1) 0) w &&& mask (decide (a = n + 1))) =
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
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (oddReg k) = mask (decide (ao = k))) ∧
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (evenReg k) = mask (decide (ae = k))) ∧
  s.gpr .x22 = zeroBit ao ∧ s.gpr .x8 = zeroBit ae

theorem Masks.of_keeps {ao ae : Nat} {s t : State} (h : Masks ao ae s)
    (k : Keeps [.x9, .x2, .x4, .x5] s t) : Masks ao ae t := by
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, by rw [k.gpr _ (by decide)]; exact h.2.2.1,
    by rw [k.gpr _ (by decide)]; exact h.2.2.2⟩
  · rw [k.gpr _ (odd_regs j (by omega))]; exact h.1 j h1 h8
  · rw [k.gpr _ (even_regs j (by omega))]; exact h.2.1 j h1 h8

/-- The candidates' words `w` of coordinate `c` of the table at `x9`: entry `m + 1`'s at
`256 c + 32 m + 8 w`. -/
def Cands (s : State) (vs : List Spec.X25519.Fe) (c w : Nat) : Prop :=
  ∀ m < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 8 * w)) 8 ∧
    s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 8 * w)) 64 = feWord (vs.getD (m + 1) 0) w

theorem Cands.of_keeps {s t : State} {vs : List Spec.X25519.Fe} {c w : Nat} (h : Cands s vs c w)
    (k : Keeps [.x2, .x4, .x5] s t) : Cands t vs c w := fun m hm => by
  rw [k.gpr .x9 (by decide), k.rd, k.wr, k.mem]; exact h m hm

theorem selectCands_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s)
    (vs : List Spec.X25519.Fe) {c w : Nat} (hc : c < 3) (hw : w < 4) (ht : Cands s vs c w) (n : Nat)
    (hn : n ≤ 8) (h0 : s.gpr .x4 = selWord vs ao 0 w ∧ s.gpr .x5 = selWord vs ae 0 w) :
    WP isa (.block ((List.range n).flatMap fun m => selectCand (256 * c + 32 * m + 8 * w) (m + 1))) s
      fun t => t.gpr .x4 = selWord vs ao n w ∧ t.gpr .x5 = selWord vs ae n w ∧
        Keeps [.x2, .x4, .x5] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨h0.1, h0.2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t4, t5, kt⟩ => ?_
    have tm := hm.of_keeps (kt.mono (by simp))
    obtain ⟨hr, hv⟩ := ht.of_keeps kt n (by omega)
    refine WP.mono (cand_ok t (by omega : n + 1 < 9) ⟨by omega, by omega⟩ hr hv)
      fun u ⟨u4, u5, ku⟩ => ⟨?_, ?_, kt.trans ku⟩
    · rw [u4, t4, tm.1 (n + 1) (by omega) (by omega), sel_step]
    · rw [u5, t5, tm.2.1 (n + 1) (by omega) (by omega), sel_step]

private theorem movz0 : (((0 : BitVec 16).setWidth 32).setWidth 64) = 0 := by decide

theorem selectStart_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s) (one : Bool)
    (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0) (w : Nat) (hw : w < 4) :
    WP isa (.block (selectStart one w)) s fun t =>
      t.gpr .x4 = selWord vs ao 0 w ∧ t.gpr .x5 = selWord vs ae 0 w ∧
        Keeps [.x4, .x5] s t := by
  have hz : ∀ a, (if (one && w == 0) = true then zeroBit a else 0) = selWord vs a 0 w := fun a => by
    unfold selWord zeroBit
    by_cases ha : a = 0
    · subst ha
      have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
      simp only [Nat.le_refl, ↓reduceIte, h0]
      cases one <;> rcases this with rfl | rfl | rfl | rfl <;> decide
    · simp [ha, show ¬ a ≤ 0 by omega]
  rw [← hz ao, ← hz ae]
  unfold selectStart
  by_cases h : (one && w == 0) = true
  · simp only [h, ↓reduceIte]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      read_x, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_true, ite_false, reduceCtorEq,
      hm.2.2.1, hm.2.2.2, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, RegUpd.gpr_write, ite_false, reduceCtorEq,
      Nat.mul_zero, BitVec.shiftLeft_zero, movz0, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `m'` agrees with `m` but on the `n` bytes at offsets `o` and `e` of `base`. -/
def Frame2 (base : Addr) (o e n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → (ofs base x < e ∨ e + n ≤ ofs base x) → m' x = m x

theorem Frame2.trans {base : Addr} {o e n : Nat} {m₁ m₂ m₃ : Mem} (h : Frame2 base o e n m₁ m₂)
    (k : Frame2 base o e n m₂ m₃) : Frame2 base o e n m₁ m₃ :=
  fun x h1 h2 => (k x h1 h2).trans (h x h1 h2)

theorem Frame2.mono {base : Addr} {o e n o' e' n' : Nat} {m m' : Mem} (h : Frame2 base o e n m m')
    (h1 : o' ≤ o) (h2 : o + n ≤ o' + n') (h3 : e' ≤ e) (h4 : e + n ≤ e' + n') :
    Frame2 base o' e' n' m m' := fun x a b => h x (by omega) (by omega)

theorem Frame2.word {base : Addr} {o e n : Nat} {m m' : Mem} (h : Frame2 base o e n m m') {d : Nat}
    (h1 : d + 8 ≤ o ∨ o + n ≤ d) (h2 : d + 8 ≤ e ∨ e + n ≤ d) (hd : d + 8 < 2 ^ 64) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Frame2.F {base : Addr} {o e n : Nat} {m m' : Mem} (h : Frame2 base o e n m m') {d : Nat}
    (h1 : d + 32 ≤ o ∨ o + n ≤ d) (h2 : d + 32 ≤ e ∨ e + n ≤ d) (hd : d + 32 < 2 ^ 64) :
    F m' base d = F m base d := by
  change toFe (AArch64.fe m' base d) = toFe (AArch64.fe m base d)
  unfold AArch64.fe
  rw [h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega),
    h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega)]

/-- What a selection leaves of the registers. -/
def RegsKept (s t : State) : Prop :=
  (∀ r, r ∉ [Reg.x9, .x2, .x4, .x5] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem RegsKept.trans {s t u : State} (h : RegsKept s t) (k : RegsKept t u) : RegsKept s u :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.trans h.2.2.2⟩

theorem RegsKept.of_keeps {s t : State} (k : Keeps [.x9, .x2, .x4, .x5] s t) : RegsKept s t :=
  ⟨k.gpr, k.rd, k.wr, k.sp⟩

theorem Masks.of_kept {ao ae : Nat} {s t : State} (h : Masks ao ae s) (k : RegsKept s t) :
    Masks ao ae t := by
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, by rw [k.1 _ (by decide)]; exact h.2.2.1,
    by rw [k.1 _ (by decide)]; exact h.2.2.2⟩
  · rw [k.1 _ (odd_regs j (by omega))]; exact h.1 j h1 h8
  · rw [k.1 _ (even_regs j (by omega))]; exact h.2.1 j h1 h8

theorem selectWord_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hm : Masks ao ae s)
    (one : Bool) (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {c o e : Nat} (hc : c < 3) (ho : o % 8 = 0) (he : e % 8 = 0)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (w : Nat) (hw : w < 4) (ht : Cands s vs c w) :
    WP isa (.block (selectWord one c o e w)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 8 * w)) (selWord vs ao 8 w)).writeW (off base (e + 8 * w))
        (selWord vs ae 8 w) ∧ RegsKept s t ∧ t.gpr .x9 = s.gpr .x9 := by
  have _hcap : workSize true = 8192 := rfl
  rw [selectWord, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selectStart_ok s hm one vs h0 w hw) fun a ⟨a4, a5, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok a (hm.of_keeps (ka.mono (by simp))) vs hc hw
    (ht.of_keeps (ka.mono (by simp))) 8 (le_refl _) ⟨a4, a5⟩) fun b ⟨b4, b5, kb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    store_sc hsb (show (o + 8 * w) % 8 = 0 by omega) (by omega),
    store_sc (hsb.setMem _) (show (e + 8 * w) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left', b4, b5]
  exact ⟨by rw [kb.mem, ka.mem], (RegsKept.of_keeps (ka.mono (by simp))).trans
    ⟨fun r hr => kb.gpr r (fun hm => hr (List.mem_cons_of_mem _ hm)), kb.rd, kb.wr, kb.sp⟩,
    by rw [kb.gpr _ (by decide), ka.gpr _ (by decide)]⟩

/-- The candidates of every word, beyond the working space at `base`. -/
def CandsFar (s : State) (base : Addr) (vs : List Spec.X25519.Fe) (c : Nat) : Prop :=
  ∀ w < 4, Cands s vs c w ∧ ∀ m < 8, ∀ b < 8,
    8192 ≤ ofs base (s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 8 * w) + BitVec.ofNat 64 b)

/-- The candidates survive the registers' and the working space's changes. -/
theorem CandsFar.of_frame2 {s t : State} {base : Addr} {vs : List Spec.X25519.Fe} {c : Nat}
    (h : CandsFar s base vs c) (k : RegsKept s t) (h9 : t.gpr .x9 = s.gpr .x9) {o e : Nat}
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (hm : Frame2 base o e 32 s.mem t.mem) :
    CandsFar t base vs c := fun w hw => by
  obtain ⟨hc, hf⟩ := h w hw
  refine ⟨fun m hm' => ?_, by rw [h9]; exact hf⟩
  obtain ⟨hr, hv⟩ := hc m hm'
  rw [h9, k.2.1, k.2.2.1]
  refine ⟨hr, ?_⟩
  rw [← hv]
  exact Mem.readW_congr fun b hb' => hm _ (by have := hf m hm' b (by omega); omega)
    (by have := hf m hm' b (by omega); omega)

theorem selectFieldPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat}
    (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {c o e : Nat} (hc : c < 3) (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (hcf : CandsFar s base vs c) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord one c o e w)) s fun t =>
      (∀ w < n, word t.mem base (o + 8 * w) = selWord vs ao 8 w ∧
        word t.mem base (e + 8 * w) = selWord vs ae 8 w) ∧
      Frame2 base o e 32 s.mem t.mem ∧ RegsKept s t ∧ t.gpr .x9 = s.gpr .x9 := by
  induction n with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun _ _ _ => rfl,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, tf, kt, t9⟩ => ?_
    have ht : Scr t base := ⟨(kt.1 _ (by decide)).trans hs.x0, kt.2.2.1 ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (selectWord_ok ht (hm.of_kept kt) one vs h0 hc ho he hb hbe n (by omega)
      ((hcf.of_frame2 kt t9 hb hbe tf) n (by omega)).1)
      fun u ⟨um, ku, u9⟩ => ⟨fun w hw => ?_, ?_, kt.trans ku, u9.trans t9⟩
    · rw [um]
      by_cases hwn : w = n
      · subst hwn
        refine ⟨?_, word_writeW_self _ _ _ _⟩
        rw [word_writeW_sep _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
      · have hwl : w < n := by omega
        rw [word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]
        exact tv w hwl
    · rw [um]
      refine tf.trans fun x h1 h2 => ?_
      rw [write_outside _ _ _ (by omega) (by omega) (by omega) h2,
        write_outside _ _ _ (by omega) (by omega) (by omega) h1]

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem selectField_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {c o e : Nat} (hc : c < 3) (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (hcf : CandsFar s base vs c) :
    WP isa (.block (selectField one c o e)) s fun t =>
      F t.mem base o = vs.getD ao 0 ∧ F t.mem base e = vs.getD ae 0 ∧
      Frame2 base o e 32 s.mem t.mem ∧ RegsKept s t ∧ t.gpr .x9 = s.gpr .x9 := by
  refine WP.mono (selectFieldPrefix_ok hs hm one vs h0 hc ho he hoe hb hbe hcf 4 (le_refl _))
    fun t ⟨tv, tf, kt, t9⟩ => ⟨?_, ?_, tf, kt, t9⟩
  · simp only [F, fe]
    have w0 := (tv 0 (by decide)).1
    have w1 := (tv 1 (by decide)).1
    have w2 := (tv 2 (by decide)).1
    have w3 := (tv 3 (by decide)).1
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]
    simp only [selWord, show ao ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]
  · simp only [F, fe]
    have w0 := (tv 0 (by decide)).2
    have w1 := (tv 1 (by decide)).2
    have w2 := (tv 2 (by decide)).2
    have w3 := (tv 3 (by decide)).2
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]
    simp only [selWord, show ae ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

/-- Coordinate `c` of a cached point in the tables: `Y - X`, `Y + X`, `2dT`. -/
def coord : Nat → Spec.Ed25519.Point → Spec.X25519.Fe
  | 0, p => p.X
  | 1, p => p.Y
  | _, p => p.Z

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

/-! ## The tables' words -/

/-- Word `96 j + 32 c + 4 m + w` of the tables is word `w` of coordinate `c` of entry `m + 1` of
table `j`. -/
theorem combWord_eq {j c m w : Nat} (hc : c < 3) (hm : m < 8) (hw : w < 4) :
    combWord (96 * j + 32 * c + 4 * m + w) = feWord (coord c (combCached j (m + 1))) w := by
  have e1 : (96 * j + 32 * c + 4 * m + w) / 96 = j := by omega
  have e2 : (96 * j + 32 * c + 4 * m + w) % 32 / 4 + 1 = m + 1 := by omega
  have e3 : (96 * j + 32 * c + 4 * m + w) % 4 = w := by omega
  have e4 : (96 * j + 32 * c + 4 * m + w) % 96 = 32 * c + 4 * m + w := by omega
  unfold combWord
  simp only [e1, e2, e3, e4]
  refine congrArg (feWord · w) ?_
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · simp only [show 32 * 0 + 4 * m + w < 32 from by omega, ite_true]; rfl
  · simp only [show ¬ 32 * 1 + 4 * m + w < 32 from by omega, show 32 * 1 + 4 * m + w < 64 from by omega,
      ite_true, ite_false]; rfl
  · simp only [show ¬ 32 * 2 + 4 * m + w < 32 from by omega, show ¬ 32 * 2 + 4 * m + w < 64 from by omega,
      ite_false]; rfl

/-- `x9` = table `j`'s address, from the static's and `x19 = j`. -/
theorem tblAddr_ok (s : State) {T : Addr} (hT : s.syms combSym = T) {j : Nat} (hj : j < 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block tblAddr) s fun t =>
      t.gpr .x9 = T + BitVec.ofNat 64 (768 * j) ∧ Keeps [.x9, .x2] s t := by
  have hsh : BitVec.ofNat 64 j <<< 8 = BitVec.ofNat 64 (256 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 256 * j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show j * 2 ^ 8 < 2 ^ 64 by omega)]
    omega
  have h3 : T + BitVec.ofNat 64 (256 * j) + BitVec.ofNat 64 (256 * j) + BitVec.ofNat 64 (256 * j) =
      T + BitVec.ofNat 64 (768 * j) := by
    rw [tbl_add T _ _, tbl_add T _ _, show 256 * j + 256 * j + 256 * j = 768 * j by omega]
  apply WP.of_runBlock
  simp only [tblAddr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 8 < 64 from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, hc, hT, hsh, h3, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Table `j`'s candidates for coordinate `c`, from the tables at `T`. -/
theorem candsFar_of_tbl {s : State} {base T : Addr} (h : TblAt s base T) {j : Nat} (hj : j < 32)
    (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j)) {c : Nat} (hc : c < 3) :
    CandsFar s base (((List.range 9).map (combCached j)).map (coord c)) c := fun w hw => by
  -- Word `w` of entry `m + 1` is word `96 j + 32 c + 4 m + w` of the tables.
  have addr : ∀ m < 8, ∀ b < 8, s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 8 * w) +
      BitVec.ofNat 64 b = T + BitVec.ofNat 64 (8 * (96 * j + 32 * c + 4 * m + w) + b) :=
    fun m hm b hb => by
      rw [hx9, tbl_add T _ _, tbl_add T _ _, show 768 * j + (256 * c + 32 * m + 8 * w) + b =
        8 * (96 * j + 32 * c + 4 * m + w) + b by omega]
  refine ⟨fun m hm => ?_, fun m hm b hb => ?_⟩
  · have hi : 96 * j + 32 * c + 4 * m + w < 32 * 96 := by omega
    have a0 := addr m hm 0 (by decide)
    rw [BitVec.add_zero, Nat.add_zero] at a0
    rw [a0]
    refine ⟨VG.CallLay.inRegions_sub h.rd (by omega) (by decide), ?_⟩
    rw [h.val _ hi, combWord_eq hc hm hw, entries_getD j (m + 1) (by omega)]
  · rw [addr m hm b hb]
    exact h.far _ (by omega)

/-- **Table `j`'s entries** for both digits, `|d| = ao` and `ae`, from the tables at `T`. -/
theorem combSelect_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {j : Nat} (hj : j < 32) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks ao ae s) :
    WP isa (.block combSelect) s fun t =>
      cachedAt (env t.mem base) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem base) 13 14 15 = combCached j ae ∧
      Frame2 base (offset 4) (offset 13) 96 s.mem t.mem ∧ RegsKept s t := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tblAddr_ok s hT hj hc) fun a ⟨a9, ka⟩ => ?_
  have hsa : Scr a base := hs.of_keeps ka (by decide)
  have hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr]) (fun x _ => by rw [ka.mem])
  have kra : RegsKept s a := RegsKept.of_keeps (ka.mono (by simp))
  have hma : Masks ao ae a := hm.of_kept kra
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hsa hao hae hma true _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (c := 0) (o := offset 4) (e := offset 13) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (candsFar_of_tbl hta hj a9 (by decide)))
    fun b ⟨b4, b13, bf, kb, b9⟩ => ?_
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hsa.x0, kb.2.2.1 ▸ hsa.wr, hs.nowrap⟩
  have htb' : TblAt b base T := hta.of_far (by rw [kb.2.1, kb.2.2.1])
    (fun x hx => bf x (Or.inr (by simp only [offset]; omega)) (Or.inr (by simp only [offset]; omega)))
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hsb hao hae (hma.of_kept kb) true _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (c := 1) (o := offset 5) (e := offset 14) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (candsFar_of_tbl htb' hj (b9.trans a9) (by decide)))
    fun c ⟨c5, c14, cf, kc, c9⟩ => ?_
  have hsc : Scr c base := ⟨(kc.1 _ (by decide)).trans hsb.x0, kc.2.2.1 ▸ hsb.wr, hs.nowrap⟩
  have htc : TblAt c base T := htb'.of_far (by rw [kc.2.1, kc.2.2.1])
    (fun x hx => cf x (Or.inr (by simp only [offset]; omega)) (Or.inr (by simp only [offset]; omega)))
  refine WP.mono (selectField_ok hsc hao hae ((hma.of_kept kb).of_kept kc) false _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (c := 2) (o := offset 6) (e := offset 15) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (candsFar_of_tbl htc hj (c9.trans (b9.trans a9)) (by decide)))
    fun t ⟨t6, t15, tf, kt, _⟩ => ⟨?_, ?_, ?_, ((kra.trans kb).trans kc).trans kt⟩
  · rw [entries_getD j ao hao] at b4 c5 t6
    refine cachedAt_eq (combCached_T j ao) ?_ ?_ t6
    · change F t.mem base (offset 4) = _
      rw [tf.F (by decide) (by decide) (by decide), cf.F (by decide) (by decide) (by decide), b4]; rfl
    · change F t.mem base (offset 5) = _
      rw [tf.F (by decide) (by decide) (by decide), c5]; rfl
  · rw [entries_getD j ae hae] at b13 c14 t15
    refine cachedAt_eq (combCached_T j ae) ?_ ?_ t15
    · change F t.mem base (offset 13) = _
      rw [tf.F (by decide) (by decide) (by decide), cf.F (by decide) (by decide) (by decide), b13]; rfl
    · change F t.mem base (offset 14) = _
      rw [tf.F (by decide) (by decide) (by decide), c14]; rfl
  · have ka' : Frame2 base (offset 4) (offset 13) 96 s.mem a.mem := fun x _ _ => by rw [ka.mem]
    exact (((ka'.trans (bf.mono (by decide) (by decide) (by decide) (by decide))).trans
      (cf.mono (by decide) (by decide) (by decide) (by decide))).trans
      (tf.mono (by decide) (by decide) (by decide) (by decide)))

end VG.Proof.Ed25519.AArch64
