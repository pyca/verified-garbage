import VerifiedGarbage.Proof.Ed25519.X86.CombDigit
import VerifiedGarbage.Proof.Ed25519.X86.CombTbl
import VerifiedGarbage.Proof.Framework.ReadHalves

/-!
# The comb's constant-time selection, for two digits at once

With the word at `combOddMasks + 4k` (`combEvenMasks + 4k`) all ones exactly
for `k` the odd (even) digit's magnitude, `selectWord` loads every candidate
word from the table once, ANDs it with both digits' masks and ORs it into
`ebx` and `ebp`, so only each digit's candidate survives, and stores them.
The tables are at `P` (`TblAt`: readable, apart from the workspace, and their
words); 32-bit word `w` of coordinate `c` of entry `m + 1` of table `j` is
half of a 64-bit word of the static (`tbl_word`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519 VG.Impl.Ed25519.X86 VG.Proof.Ed25519
open VG.Impl.X25519.X86 (sc at_)

/-- The masks of both digits' magnitudes `ao` and `ae`, in memory. -/
def Masks (x : BitVec 32) (ao ae : Nat) (m : Mem) : Prop :=
  (∀ k < 9, wd m x (combOddMasks + 4 * k) = mask (decide (ao = k)).toNat) ∧
  (∀ k < 9, wd m x (combEvenMasks + 4 * k) = mask (decide (ae = k)).toNat)

theorem or0 (v : BitVec 32) : v ||| 0 = v := by ext i; simp
theorem zor (v : BitVec 32) : 0 ||| v = v := by ext i; simp

theorem mask_and (v : BitVec 32) (b : Bool) : v &&& mask b.toNat = if b then v else 0 := by
  cases b
  · show v &&& mask 0 = 0
    rw [show mask 0 = 0 by decide]; ext i; simp
  · show v &&& mask 1 = v
    rw [show mask 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

/-- The masks survive stores below them. -/
theorem Masks.frame {x : BitVec 32} {ao ae : Nat} {m m' : Mem} (h : Masks x ao ae m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ d, 1024 ≤ d → d + 4 ≤ 1160 → ∀ r ∈ rs, (sub x d 4).Disjoint r) :
    Masks x ao ae m' :=
  ⟨fun k hk => (wd_frame hf (hd _ (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks]; omega))).trans (h.1 k hk),
    fun k hk => (wd_frame hf (hd _ (by simp only [combEvenMasks]; omega)
      (by simp only [combEvenMasks]; omega))).trans (h.2 k hk)⟩

/-! ## The tables -/

/-- Coordinate `c` of a cached point: `Y - X`, `Y + X`, `2dT`. -/
def coord (c : Nat) (e : Spec.Ed25519.Point) : Spec.X25519.Fe :=
  if c = 0 then e.X else if c = 1 then e.Y else e.Z

theorem setWidth_ofNat64 (n : Nat) : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd n (by decide)

theorem extract_ofNat64 (n : Nat) :
    (BitVec.ofNat 64 n).extractLsb' 32 32 = BitVec.ofNat 32 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self, Nat.mod_mod]

theorem combWord_eq {j c m k : Nat} (hc : c < 3) (hm : m < 8) (hk : k < 4) :
    combWord (96 * j + 32 * c + 4 * m + k) =
      BitVec.ofNat 64 ((coord c (combCached j (m + 1))).val / 2 ^ (64 * k)) := by
  have e1 : (96 * j + 32 * c + 4 * m + k) / 96 = j := by omega
  have e2 : (96 * j + 32 * c + 4 * m + k) % 32 / 4 = m := by omega
  have e3 : (96 * j + 32 * c + 4 * m + k) % 96 = 32 * c + 4 * m + k := by omega
  have e4 : (96 * j + 32 * c + 4 * m + k) % 4 = k := by omega
  simp only [combWord, e1, e2, e3, e4]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · simp only [coord, show 32 * 0 + 4 * m + k < 32 by omega, ↓reduceIte]
  · simp only [coord, show ¬ 32 * 1 + 4 * m + k < 32 by omega, show 32 * 1 + 4 * m + k < 64 by omega,
      ↓reduceIte, Nat.one_ne_zero]
  · simp only [coord, show ¬ 32 * 2 + 4 * m + k < 32 by omega, show ¬ 32 * 2 + 4 * m + k < 64 by omega,
      ↓reduceIte, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide]

theorem feWord_even (v : Spec.X25519.Fe) (k : Nat) :
    feWord v (2 * k) = BitVec.ofNat 32 (v.val / 2 ^ (64 * k)) := by
  unfold feWord
  rw [← Nat.pow_mul, show 32 * (2 * k) = 64 * k by omega]

theorem feWord_odd (v : Spec.X25519.Fe) (k : Nat) :
    feWord v (2 * k + 1) = BitVec.ofNat 32 (v.val / 2 ^ (64 * k) / 2 ^ 32) := by
  unfold feWord
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_mul, show 32 * (2 * k + 1) = 64 * k + 32 by omega]

/-- Word `w` (of 32 bits) of coordinate `c` of entry `n + 1` of table `j`, in the static's
words at `T`. -/
theorem tbl_word {m : Mem} {T : Addr} (h : TblWords T m) {j c n w : Nat} (hj : j < 32)
    (hc : c < 3) (hn : n < 8) (hw : w < 8) :
    m.readW (T + BitVec.ofNat 64 (768 * j + 256 * c + 32 * n + 4 * w)) 32 =
      feWord (coord c (combCached j (n + 1))) w := by
  obtain ⟨k, hk⟩ : ∃ k, w = 2 * k ∨ w = 2 * k + 1 := ⟨w / 2, by omega⟩
  have hi : 96 * j + 32 * c + 4 * n + k < combWords.length := by rw [combWords_length]; omega
  have h64 := h _ hi
  rw [combWords_getD (by omega), combWord_eq hc hn (by omega)] at h64
  rcases hk with rfl | rfl
  · rw [show 768 * j + 256 * c + 32 * n + 4 * (2 * k) = 8 * (96 * j + 32 * c + 4 * n + k) by omega,
      Mem.readW_lo32 h64, setWidth_ofNat64, feWord_even]
  · rw [show 768 * j + 256 * c + 32 * n + 4 * (2 * k + 1) = 8 * (96 * j + 32 * c + 4 * n + k) + 4 by omega,
      ← Offset.add_add, Mem.readW_hi32 h64, extract_ofNat64, feWord_odd]

/-- The comb's tables at `P` in `s`: in 32-bit memory, readable, their words, apart from the
workspace at `x`. -/
structure TblAt (x P : BitVec 32) (s : State) : Prop where
  fit : P.toNat + 8 * combWords.length ≤ 2 ^ 32
  rd : TBL (P.setWidth 64) ∈ s.rd
  words : TblWords (P.setWidth 64) s.mem
  far : (TBL (P.setWidth 64)).Disjoint (scR 8192 x)

/-- The tables survive writes to the workspace. -/
theorem TblAt.of_frame {x P : BitVec 32} {s t : State} (h : TblAt x P s) (hrd : t.rd = s.rd)
    {rs : List Region} (hf : Frame rs s.mem t.mem) (hrs : ∀ r ∈ rs, Region.Sub r (scR 8192 x)) :
    TblAt x P t := by
  have hl := combWords_length
  refine ⟨h.fit, hrd ▸ h.rd, fun i hi => ?_, h.far⟩
  rw [← h.words i hi]
  exact hf.readW (r := TBL (P.setWidth 64)) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => h.far.sub_right (hrs r hr)) (by decide)

/-- `[P + a + d]`, in 32-bit memory. -/
theorem tbl_addr {P : BitVec 32} {a d : Nat} (h : P.toNat + a + d < 2 ^ 32) :
    addr (P + BitVec.ofNat 32 a) d = P.setWidth 64 + BitVec.ofNat 64 (a + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Word `w` of coordinate `c` of entry `n + 1` of table `j`, at `[ecx + 256 c + 32 n + 4 w]`
for `ecx` table `j`'s address: readable, and its value. -/
theorem TblAt.cand {x P : BitVec 32} {s : State} (h : TblAt x P s) {j c n w : Nat} (hj : j < 32)
    (hc : c < 3) (hn : n < 8) (hw : w < 8) :
    InRegions (s.rd ++ s.wr) (addr (P + BitVec.ofNat 32 (768 * j)) (256 * c + 32 * n + 4 * w)) 4 ∧
      s.mem.readW (addr (P + BitVec.ofNat 32 (768 * j)) (256 * c + 32 * n + 4 * w)) 32 =
        feWord (coord c (combCached j (n + 1))) w := by
  have hf := h.fit
  rw [combWords_length] at hf
  rw [tbl_addr (by omega)]
  refine ⟨⟨_, List.mem_append_left _ h.rd, Offset.contains_base _ (by rw [combWords_length]; omega)
    (by omega)⟩, ?_⟩
  rw [show 768 * j + (256 * c + 32 * n + 4 * w) = 768 * j + 256 * c + 32 * n + 4 * w by omega]
  exact tbl_word h.words hj hc hn hw

/-! ## The selection -/

theorem selectCand_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) {d k : Nat} (hk : k < 9) {v : BitVec 32}
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) d) 4)
    (hv : s.mem.readW (addr (s.gpr .ecx) d) 32 = v) :
    WP isa (.block (selectCand d k)) s fun t =>
      t.gpr .ebx = s.gpr .ebx ||| (if ao = k then v else 0) ∧
      t.gpr .ebp = s.gpr .ebp ||| (if ae = k then v else 0) ∧
      Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧ t.mem = s.mem := by
  refine Wp.wp_ldm rfl hin fun s₁ h₁ => Wp.wp_mov fun s₂ h₂ => ?_
  have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine wp_andm (k₂.ctx hc).edi ((k₂.ctx hc).inRW (by simp only [combOddMasks]; omega) (by decide))
    fun s₃ h₃ => ?_
  have k₃ := k₂.trans (updKeep h₃)
  refine wp_andm (k₃.ctx hc).edi ((k₃.ctx hc).inRW (by simp only [combEvenMasks]; omega) (by decide))
    fun s₄ h₄ => Wp.wp_or fun s₅ h₅ => Wp.wp_or fun s₆ h₆ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [h₃.mem, m₂]
  refine ⟨?_, ?_, k₃.trans ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆))), ?_,
    by rw [h₆.mem, h₅.mem, h₄.mem, m₃]⟩
  · rw [h₆.other .ebx (by decide), h₅.gpr, h₄.other .ebx (by decide), h₄.other .eax (by decide),
      h₃.gpr, h₃.other .ebx (by decide), h₂.other .ebx (by decide), h₂.other .eax (by decide),
      h₁.gpr, h₁.other .ebx (by decide), m₂, hv]
    change _ ||| (v &&& wd s.mem x (combOddMasks + 4 * k)) = _
    rw [hm.1 k hk, mask_and]
    by_cases e : ao = k <;> simp [e]
  · rw [h₆.gpr, h₅.other .ebp (by decide), h₅.other .edx (by decide), h₄.gpr,
      h₄.other .ebp (by decide), h₃.other .ebp (by decide), h₃.other .edx (by decide), h₂.gpr,
      h₂.other .ebp (by decide), h₁.gpr, h₁.other .ebp (by decide), m₃, hv]
    change _ ||| (v &&& wd s.mem x (combEvenMasks + 4 * k)) = _
    rw [hm.2 k hk, mask_and]
    by_cases e : ae = k <;> simp [e]
  · rw [h₆.other .ecx (by decide), h₅.other .ecx (by decide), h₄.other .ecx (by decide),
      h₃.other .ecx (by decide), h₂.other .ecx (by decide), h₁.other .ecx (by decide)]

/-- The value of entry 0 (the identity's: `1` in word 0 of `Y - X` and `Y + X`, if `one`). -/
theorem feWord_start (one : Bool) (w : Nat) :
    feWord (if one then 1 else 0) w = if one && w == 0 then 1 else 0 := by
  cases one
  · simp [feWord]
  · rcases Nat.eq_zero_or_pos w with rfl | hw
    · rfl
    · have h1 : (1 : Spec.X25519.Fe).val / (2 ^ 32) ^ w = 0 :=
        Nat.div_eq_of_lt (by show 1 < _; exact Nat.one_lt_pow (by omega) (by decide))
      have h2 : (true && w == 0) = false := by simp only [Bool.true_and, beq_eq_false_iff_ne]; omega
      rw [h2]
      show BitVec.ofNat 32 ((1 : Spec.X25519.Fe).val / (2 ^ 32) ^ w) = _
      rw [h1]; rfl

theorem mask_one (b : Bool) : mask b.toNat &&& (1 : BitVec 32) = if b then 1 else 0 := by
  cases b <;> decide

theorem selectStart_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (one : Bool) (w : Nat) :
    WP isa (.block (selectStart one w)) s fun t =>
      t.gpr .ebx = (if ao = 0 then feWord (if one then 1 else 0) w else 0) ∧
      t.gpr .ebp = (if ae = 0 then feWord (if one then 1 else 0) w else 0) ∧
      Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧ t.mem = s.mem := by
  rw [feWord_start]
  unfold selectStart
  split
  · refine Wp.wp_ldm hc.edi (hc.inRW (by simp only [combOddMasks]; omega) (by decide)) fun s₁ h₁ => ?_
    refine Wp.wp_andi fun s₂ h₂ => ?_
    have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
    have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
    refine Wp.wp_ldm (k₂.ctx hc).edi ((k₂.ctx hc).inRW (by simp only [combEvenMasks]; omega)
      (by decide)) fun s₃ h₃ => Wp.wp_andi fun s₄ h₄ => WP.block_nil ?_
    refine ⟨?_, ?_, k₂.trans ((updKeep h₃).trans (updKeep h₄)), ?_, by rw [h₄.mem, h₃.mem, m₂]⟩
    · rw [h₄.other .ebx (by decide), h₃.other .ebx (by decide), h₂.gpr, h₁.gpr]
      have := hm.1 0 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at this
      change wd s.mem x combOddMasks &&& 1 = _
      rw [this, mask_one]
      by_cases e : ao = 0 <;> simp [e]
    · rw [h₄.gpr, h₃.gpr, m₂]
      have := hm.2 0 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at this
      change wd s.mem x combEvenMasks &&& 1 = _
      rw [this, mask_one]
      by_cases e : ae = 0 <;> simp [e]
    · rw [h₄.other .ecx (by decide), h₃.other .ecx (by decide), h₂.other .ecx (by decide),
        h₁.other .ecx (by decide)]
  · simp only [ite_self]
    refine Wp.wp_movi fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => WP.block_nil ?_
    exact ⟨by rw [h₂.other .ebx (by decide), h₁.gpr], h₂.gpr, (updKeep h₁).trans (updKeep h₂),
      by rw [h₂.other .ecx (by decide), h₁.other .ecx (by decide)], by rw [h₂.mem, h₁.mem]⟩

/-- The candidates `1 … n`'s word, of the value `f k` for candidate `k`, for the magnitude `a`. -/
def selRange (f : Nat → BitVec 32) (a n : Nat) : BitVec 32 := if 0 < a ∧ a ≤ n then f a else 0

theorem selRange_step (f : Nat → BitVec 32) (a n : Nat) :
    selRange f a n ||| (if a = n + 1 then f (n + 1) else 0) = selRange f a (n + 1) := by
  unfold selRange
  by_cases h : 0 < a ∧ a ≤ n
  · simp only [h, and_self, ↓reduceIte, show 0 < a ∧ a ≤ n + 1 by omega, show ¬ a = n + 1 by omega, or0]
  · by_cases he : a = n + 1
    · subst he
      have e2 : 0 < n + 1 ∧ n + 1 ≤ n + 1 := by omega
      simp only [h, ↓reduceIte]
      simp only [e2, and_self, ↓reduceIte, zor]
    · simp only [h, he, ↓reduceIte, show ¬ (0 < a ∧ a ≤ n + 1) by omega, or0]

/-- Table `j`'s address in `ecx`. -/
abbrev TblReg (P : BitVec 32) (j : Nat) (s : State) : Prop := s.gpr .ecx = P + BitVec.ofNat 32 (768 * j)

theorem selectCands_ok {x P : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (ht : TblAt x P s) {j c w : Nat} (hj : j < 32) (hc3 : c < 3)
    (hw : w < 8) (hq : TblReg P j s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun m => selectCand (256 * c + 32 * m + 4 * w) (m + 1))) s
      fun t =>
        t.gpr .ebx = s.gpr .ebx ||| selRange (fun k => feWord (coord c (combCached j k)) w) ao n ∧
        t.gpr .ebp = s.gpr .ebp ||| selRange (fun k => feWord (coord c (combCached j k)) w) ae n ∧
        Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧ t.mem = s.mem
  | 0, _ => WP.block_nil ⟨by simp only [selRange, Nat.le_zero, show ¬ (0 < ao ∧ ao = 0) by omega,
      ↓reduceIte, or0], by simp only [selRange, Nat.le_zero, show ¬ (0 < ae ∧ ae = 0) by omega,
      ↓reduceIte, or0], Keep.refl _, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (selectCands_ok hc hm ht hj hc3 hw hq n (by omega))
      fun t ⟨tb, tp, kt, et, mt⟩ => ?_)
    obtain ⟨hin, hv⟩ := ht.cand hj hc3 (show n < 8 by omega) hw
    rw [← hq, ← et] at hin hv
    rw [← mt] at hv
    refine WP.mono (selectCand_ok (ao := ao) (ae := ae) (kt.ctx hc) (by rw [mt]; exact hm)
      (show n + 1 < 9 by omega) (by rw [← kt.rd, ← kt.wr] at hin; exact hin) hv)
      fun u ⟨ub, up, ku, eu, mu⟩ => ⟨?_, ?_, kt.trans ku, eu.trans et, mu.trans mt⟩
    · rw [ub, tb, BitVec.or_assoc, selRange_step]
    · rw [up, tp, BitVec.or_assoc, selRange_step]

/-- Word `w` of entry `a`'s coordinate `c` of table `j`. -/
abbrev candWord (j c w a : Nat) : BitVec 32 := feWord (coord c (combCached j a)) w

theorem start_range (j c w a : Nat) (ha : a < 9) (one : Bool)
    (hone : coord c (combCached j 0) = if one then 1 else 0) :
    (if a = 0 then feWord (if one then 1 else 0) w else 0) |||
      selRange (fun k => feWord (coord c (combCached j k)) w) a 8 = candWord j c w a := by
  unfold selRange
  by_cases h : a = 0
  · subst h; simp only [↓reduceIte, Nat.lt_irrefl, false_and, or0, candWord, hone]
  · simp only [h, ↓reduceIte, show 0 < a ∧ a ≤ 8 by omega, and_self, zor]

theorem selectWord_ok {x P : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) (ht : TblAt x P s) {j c : Nat} (hj : j < 32)
    (hc3 : c < 3) (hq : TblReg P j s) (one : Bool)
    (hone : coord c (combCached j 0) = if one then 1 else 0) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (w : Nat) (hw : w < 8) :
    WP isa (.block (selectWord one c o e w)) s fun t => Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧
      t.mem = (s.mem.writeW (addr x (o + 4 * w)) (candWord j c w ao)).writeW (addr x (e + 4 * w))
        (candWord j c w ae) := by
  rw [selectWord, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selectStart_ok hc hm one w) fun a ⟨ab, ap, ka, ea, ma⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok (ao := ao) (ae := ae) (ka.ctx hc) (by rw [ma]; exact hm)
    (ht.of_frame (rs := []) ka.rd (by rw [ma]; exact Frame.refl _ _) nofun) hj hc3 hw (by rw [TblReg, ea]; exact hq)
    8 (Nat.le_refl _)) fun t ⟨tb, tp, kt, et, mt⟩ => ?_
  have k₃ := ka.trans kt
  refine Wp.wp_stm (k₃.ctx hc).edi ((k₃.ctx hc).inW (by omega) (by decide)) fun u hu => ?_
  have ku : Keep t u := ⟨by rw [hu.gpr], by rw [hu.gpr], by rw [hu.gpr], hu.rd, hu.wr⟩
  refine Wp.wp_stm ((k₃.trans ku).ctx hc).edi (((k₃.trans ku).ctx hc).inW (by omega) (by decide))
    fun v hv => WP.block_nil ⟨k₃.trans (ku.trans ⟨by rw [hv.gpr], by rw [hv.gpr], by rw [hv.gpr],
      hv.rd, hv.wr⟩), by rw [hv.gpr, hu.gpr, et, ea], ?_⟩
  rw [hv.mem, hu.mem, hu.gpr, mt, ma, tb, tp, ab, ap, start_range j c w ao hao one hone,
    start_range j c w ae hae one hone]

/-- Two regions of the workspace (`[o, o + n)` and `[e, e + n)`) may change. -/
abbrev Frame2 (x : BitVec 32) (o e n : Nat) (m m' : Mem) : Prop := Frame [sub x o n, sub x e n] m m'

theorem selectFieldPrefix_ok {x P : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hao : ao < 9) (hae : ae < 9) (hm : Masks x ao ae s.mem) (ht : TblAt x P s) {j c : Nat}
    (hj : j < 32) (hc3 : c < 3) (hq : TblReg P j s) (one : Bool)
    (hone : coord c (combCached j 0) = if one then 1 else 0) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun w => selectWord one c o e w)) s fun t =>
      Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧ Frame2 x o e 32 s.mem t.mem ∧
      ∀ w < n, wd t.mem x (o + 4 * w) = candWord j c w ao ∧ wd t.mem x (e + 4 * w) = candWord j c w ae
  | 0, _ => WP.block_nil ⟨Keep.refl _, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hfit := hc.fit
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (selectFieldPrefix_ok hc hao hae hm ht hj hc3 hq one hone ho he
      hoe n (by omega)) fun t ⟨kt, et, ft, wt⟩ => ?_)
    have hmt : Masks x ao ae t.mem := hm.frame ft fun d h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
      · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
    have htt : TblAt x P t := ht.of_frame kt.rd ft fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [scR_eq]; exact sub_sub hfit (by omega) (by omega) (by omega)
      · rw [scR_eq]; exact sub_sub hfit (by omega) (by omega) (by omega)
    refine WP.mono (selectWord_ok (kt.ctx hc) hao hae hmt htt hj hc3 (by rw [TblReg, et]; exact hq)
      one hone ho he n (by omega)) fun u ⟨ku, eu, mu⟩ => ⟨kt.trans ku, eu.trans et, ?_, fun w hw => ?_⟩
    · rw [mu]
      refine (ft.writeW List.mem_cons_self _ ?_).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_
      · exact sub_contains (by omega) (by omega) (by omega) (by decide)
      · exact sub_contains (by omega) (by omega) (by omega) (by decide)
    · rw [mu]
      by_cases hwn : w = n
      · subst hwn
        refine ⟨?_, wd_write_self _ _ _ _⟩
        rw [wd_write_ne _ _ (by omega) (by omega) (by omega), wd_write_self]
      · have hwl : w < n := by omega
        rw [wd_write_ne _ _ (by omega) (by omega) (by omega), wd_write_ne _ _ (by omega) (by omega)
          (by omega), wd_write_ne _ _ (by omega) (by omega) (by omega),
          wd_write_ne _ _ (by omega) (by omega) (by omega)]
        exact wt w hwl

theorem feWord_num (v : Spec.X25519.Fe) :
    num (fun w => (feWord v w).toNat) 8 = v.val := by
  rw [num_congr (g := fun k => v.val / (2 ^ 32) ^ k % 2 ^ 32) (fun k _ => by
    simp only [feWord, BitVec.toNat_ofNat]), num_digits]
  exact Nat.mod_eq_of_lt (by have h := v.isLt; simp only [Spec.X25519.P] at h; omega)

theorem field_of_words {m : Mem} {x : BitVec 32} {o : Nat} {v : Spec.X25519.Fe}
    (h : ∀ w < 8, wd m x (o + 4 * w) = feWord v w) : VG.Proof.X25519.X86.F m x o = v := by
  have hf : fe m x o = v.val := by
    unfold fe
    rw [← feWord_num]
    exact num_congr fun w hw => congrArg BitVec.toNat (h w hw)
  rw [VG.Proof.X25519.X86.F, hf, VG.Proof.X25519.toFe_self]

theorem selectField_ok {x P : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) (ht : TblAt x P s) {j c : Nat} (hj : j < 32)
    (hc3 : c < 3) (hq : TblReg P j s) (one : Bool)
    (hone : coord c (combCached j 0) = if one then 1 else 0) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o) :
    WP isa (.block (selectField one c o e)) s fun t =>
      Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧ Frame2 x o e 32 s.mem t.mem ∧
      VG.Proof.X25519.X86.F t.mem x o = coord c (combCached j ao) ∧
      VG.Proof.X25519.X86.F t.mem x e = coord c (combCached j ae) :=
  WP.mono (selectFieldPrefix_ok hc hao hae hm ht hj hc3 hq one hone ho he hoe 8 (le_refl _))
    fun _ ⟨kt, et, ft, wt⟩ => ⟨kt, et, ft, field_of_words fun w hw => (wt w hw).1,
      field_of_words fun w hw => (wt w hw).2⟩

theorem Frame2.F {x : BitVec 32} {o e q : Nat} {m m' : Mem} (h : Frame2 x o e 32 m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (ho : o + 32 ≤ 8192) (he : e + 32 ≤ 8192) (hq : q + 32 ≤ 8192)
    (h1 : q + 32 ≤ o ∨ o + 32 ≤ q) (h2 : q + 32 ≤ e ∨ e + 32 ≤ q) :
    VG.Proof.X25519.X86.F m' x q = VG.Proof.X25519.X86.F m x q :=
  congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (by omega)
    · exact sub_disj (by omega) (by omega) (by omega))

theorem Frame2.widen {x : BitVec 32} {o e o' e' : Nat} {m m' : Mem} (h : Frame2 x o e 32 m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h1 : o' ≤ o) (h2 : o + 32 ≤ o' + 96) (h3 : e' ≤ e)
    (h4 : e + 32 ≤ e' + 96) (ho : o < 8192) (he : e < 8192) :
    Frame [sub x o' 96, sub x e' 96] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sub hx h1 h2 ho⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hx h3 h4 he⟩

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

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

/-- The selection's frame: slots 4–6 and 13–15. -/
abbrev SelFrame (x : BitVec 32) (m m' : Mem) : Prop := Frame [sub x (offset 4) 96, sub x (offset 13) 96] m m'


theorem coord_zero (e : Spec.Ed25519.Point) : coord 0 e = e.X := by simp [coord]
theorem coord_one (e : Spec.Ed25519.Point) : coord 1 e = e.Y := by simp [coord]
theorem coord_two (e : Spec.Ed25519.Point) : coord 2 e = e.Z := by simp [coord]

/-! ## The table's address -/

theorem tblDbl_ok : ∀ (n : Nat) {s : State} {a : Nat}, s.gpr .eax = BitVec.ofNat 32 a →
    WP isa (.block (List.replicate n (.alu .add .eax (.reg .eax)))) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .ecx = s.gpr .ecx ∧ t.gpr .eax = BitVec.ofNat 32 (2 ^ n * a)
  | 0, _, _, h => WP.block_nil ⟨Keep.refl _, rfl, rfl, by rw [h, Nat.pow_zero, Nat.one_mul]⟩
  | n + 1, s, a, h => by
    rw [List.replicate_succ]
    refine Wp.wp_add fun s₁ h₁ _ => ?_
    refine WP.mono (tblDbl_ok n (a := 2 * a) (by rw [h₁.gpr, h, ← BitVec.ofNat_add, Nat.two_mul]))
      fun t ⟨kt, mt, ct, et⟩ => ⟨(updKeep h₁).trans kt, mt.trans h₁.mem,
        ct.trans (h₁.other .ecx (by decide)), by rw [et, Nat.pow_succ, Nat.mul_assoc]⟩

theorem tblAdds_ok : ∀ (n : Nat) {s : State} {P : BitVec 32} {a b : Nat},
    s.gpr .ecx = P + BitVec.ofNat 32 b → s.gpr .eax = BitVec.ofNat 32 a →
    WP isa (.block (List.replicate n (.alu .add .ecx (.reg .eax)))) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .ecx = P + BitVec.ofNat 32 (b + n * a)
  | 0, _, _, _, b, hc, _ => WP.block_nil ⟨Keep.refl _, rfl, by rw [hc, Nat.zero_mul, Nat.add_zero]⟩
  | n + 1, s, P, a, b, hc, ha => by
    rw [List.replicate_succ]
    refine Wp.wp_add fun s₁ h₁ _ => ?_
    refine WP.mono (tblAdds_ok n (P := P) (a := a) (b := b + a)
      (by rw [h₁.gpr, hc, ha, BitVec.add_assoc, ← BitVec.ofNat_add])
      (by rw [h₁.other .eax (by decide), ha]))
      fun t ⟨kt, mt, et⟩ => ⟨(updKeep h₁).trans kt, mt.trans h₁.mem, by
        rw [et, Nat.succ_mul, Nat.add_assoc, Nat.add_comm a]⟩

theorem tblAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {j : Nat}
    (hs : s.gpr .esi = BitVec.ofNat 32 j) {P : BitVec 32} (hp : wd s.mem x combTbl = P) :
    WP isa (.block tblAddr) s fun t => Keep s t ∧ t.mem = s.mem ∧ TblReg P j t := by
  rw [show tblAddr = .mov .eax (.reg .esi) :: (List.replicate 8 (.alu .add .eax (.reg .eax)) ++
    (.mov .ecx (.mem (sc combTbl)) :: List.replicate 3 (.alu .add .ecx (.reg .eax)))) from rfl]
  refine Wp.wp_mov fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tblDbl_ok 8 (s := s₁) (a := j) (by rw [h₁.gpr, hs])) fun s₂ ⟨k₂, m₂, _, e₂⟩ => ?_
  have k := (updKeep h₁).trans k₂
  refine Wp.wp_ldm (k.ctx hc).edi ((k.ctx hc).inRW (by simp only [combTbl]; omega) (by decide))
    fun s₃ h₃ => ?_
  refine WP.mono (tblAdds_ok 3 (s := s₃) (P := P) (b := 0) (a := 2 ^ 8 * j)
    (by rw [h₃.gpr, m₂, h₁.mem, BitVec.add_zero]; exact hp)
    (by rw [h₃.other .eax (by decide), e₂])) fun t ⟨kt, mt, et⟩ =>
      ⟨k.trans ((updKeep h₃).trans kt), by rw [mt, h₃.mem, m₂, h₁.mem], ?_⟩
  rw [TblReg, et]
  congr 2
  omega

/-! ## Both entries -/

theorem combSelect_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) {j : Nat} (hj : j < 32)
    (hs : s.gpr .esi = BitVec.ofNat 32 j) {P : BitVec 32} (hp : wd s.mem x combTbl = P)
    (ht : TblAt x P s) :
    WP isa (.block combSelect) s fun t =>
      cachedAt (env t.mem x) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem x) 13 14 15 = combCached j ae ∧ Keep s t ∧ SelFrame x s.mem t.mem := by
  have hfit := hc.fit
  have mf : ∀ {m m' : Mem} {o e : Nat}, Masks x ao ae m → Frame2 x o e 32 m m' → o + 32 ≤ 1024 →
      e + 32 ≤ 1024 → Masks x ao ae m' := fun hm f ho he => hm.frame f fun d h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
    · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  have tf : ∀ {u v : State} {o e : Nat}, TblAt x P u → v.rd = u.rd → Frame2 x o e 32 u.mem v.mem →
      o + 32 ≤ 1024 → e + 32 ≤ 1024 → TblAt x P v := fun ht hr f ho he => ht.of_frame hr f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [scR_eq]; exact sub_sub hfit (by omega) (by omega) (by omega)
    · rw [scR_eq]; exact sub_sub hfit (by omega) (by omega) (by omega)
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tblAddr_ok hc hs hp) fun a ⟨ka, ma, qa⟩ => ?_
  have ca := ka.ctx hc
  have hma : Masks x ao ae a.mem := by rw [ma]; exact hm
  have hta : TblAt x P a := ht.of_frame (rs := []) ka.rd (by rw [ma]; exact Frame.refl _ _) nofun
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok ca hao hae hma hta hj (by decide) qa true
    (by simp [coord, combCached]) (o := offset 4) (e := offset 13) (by decide) (by decide)
    (by decide)) fun b ⟨kb, eb, fb, b4, b13⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok (kb.ctx ca) hao hae (mf hma fb (by decide) (by decide))
    (tf hta kb.rd fb (by decide) (by decide)) hj (by decide) (by rw [TblReg, eb]; exact qa) true
    (by simp [coord, combCached]) (o := offset 5) (e := offset 14) (by decide) (by decide)
    (by decide)) fun c ⟨kc, ec, fc, c5, c14⟩ => ?_
  refine WP.mono (selectField_ok ((kb.trans kc).ctx ca) hao hae
    (mf (mf hma fb (by decide) (by decide)) fc (by decide) (by decide))
    (tf (tf hta kb.rd fb (by decide) (by decide)) kc.rd fc (by decide) (by decide)) hj (by decide)
    (by rw [TblReg, ec, eb]; exact qa) false (by simp [coord, combCached]) (o := offset 6)
    (e := offset 15) (by decide) (by decide) (by decide))
    fun t ⟨kt, _, ft, t6, t15⟩ => ⟨?_, ?_, ka.trans ((kb.trans kc).trans kt), ?_⟩
  · rw [coord_zero] at b4
    rw [coord_one] at c5
    rw [coord_two] at t6
    refine cachedAt_eq (combCached_T j ao) ?_ ?_ t6
    · change VG.Proof.X25519.X86.F t.mem x (offset 4) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide),
        fc.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), b4]
    · change VG.Proof.X25519.X86.F t.mem x (offset 5) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), c5]
  · rw [coord_zero] at b13
    rw [coord_one] at c14
    rw [coord_two] at t15
    refine cachedAt_eq (combCached_T j ae) ?_ ?_ t15
    · change VG.Proof.X25519.X86.F t.mem x (offset 13) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide),
        fc.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), b13]
    · change VG.Proof.X25519.X86.F t.mem x (offset 14) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), c14]
  · rw [← ma]
    exact ((fb.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (fc.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans
      (ft.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

end VG.Proof.Ed25519.X86
