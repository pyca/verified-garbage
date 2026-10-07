import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath

/-!
# A candidate on AArch64: trial division by one prime

For each prime `s` of the table, `acc := (acc + h) 2^(−32) mod s` over the
32-bit halves `h` of `c` from the least significant (`redc32`, Montgomery
reduction with `−s⁻¹ mod 2^64`): `acc < 2 s` and
`acc 2^(64 w) ≡ c (mod s)`, so `s` divides `c` iff `acc` is 0 or `s`
(`trialEntry_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- The 32-bit product of `mul w`, as `redc_math` states it. -/
theorem redc_mulw_toNat (a b : BitVec 64) :
    ((a.setWidth 32 * b.setWidth 32).setWidth 64).toNat = a.toNat * b.toNat % 2 ^ 64 % 2 ^ 32 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide) : 2 ^ 32 ∣ 2 ^ 64), ← Nat.mul_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

/-- `redc32`: `acc := (acc + h) 2^(−32) mod s`, below `2 s`, for `h = x4 <
2^32`, `acc = x2 < 2 s`, `s = x13` and `−s⁻¹ = x15`. -/
theorem redc32_ok {t : State} {s : Nat} (h4 : (t.gpr .x4).toNat < 2 ^ 32) (h2 : (t.gpr .x2).toNat < 2 * s)
    (h13 : (t.gpr .x13).toNat = s) (h15 : (s * (t.gpr .x15).toNat + 1) % 2 ^ 64 = 0) (hs3 : 3 ≤ s)
    (hs : s < 2 ^ 13) :
    WP isa (.block redc32) t fun t' =>
      ((t'.gpr .x2).toNat < 2 * s ∧
      ((t'.gpr .x2).toNat * 2 ^ 32) % s = ((t.gpr .x4).toNat + (t.gpr .x2).toNat) % s ∧
      t'.mem = t.mem) ∧ Keep [.x2, .x4, .x6] t t' := by
  have hX : (t.gpr .x4 + t.gpr .x2).toNat = (t.gpr .x4).toNat + (t.gpr .x2).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hXs : (t.gpr .x4).toNat + (t.gpr .x2).toNat < s * 2 ^ 32 := by
    have : 2 * s ≤ s * 2 ^ 31 := by rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ (by decide)
    have : s * 2 ^ 31 + s * 2 ^ 31 = s * 2 ^ 32 := by rw [← Nat.mul_add]
    omega
  obtain ⟨_, hlt, hmod⟩ := redc_math (X := (t.gpr .x4).toNat + (t.gpr .x2).toNat) (sv := (t.gpr .x15).toNat) h15 hXs
  refine WP.mono (WP.keep [.x2, .x4, .x6] (Q := fun t' =>
      (t'.gpr .x2).toNat = ((t.gpr .x4).toNat + (t.gpr .x2).toNat +
        ((t.gpr .x4).toNat + (t.gpr .x2).toNat) * (t.gpr .x15).toNat % 2 ^ 64 % 2 ^ 32 * s) / 2 ^ 32 ∧
      t'.mem = t.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h, hm⟩, k⟩ => ⟨⟨by rw [h]; exact hlt, by rw [h]; exact hmod, hm⟩, k⟩
  unfold redc32
  brun [exec_mul_w]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_mul, redc_mulw_toNat, hX, h13]
  have hu : ((t.gpr .x4).toNat + (t.gpr .x2).toNat) * (t.gpr .x15).toNat % 2 ^ 64 % 2 ^ 32 < 2 ^ 32 :=
    Nat.mod_lt _ (by decide)
  generalize ((t.gpr .x4).toNat + (t.gpr .x2).toNat) * (t.gpr .x15).toNat % 2 ^ 64 % 2 ^ 32 = U at hu ⊢
  have hus : U * s < 2 ^ 45 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hu (Nat.le_of_lt hs) (by omega)) (by decide)
  rw [Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega : U * s < 2 ^ 64), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega), Nat.add_comm]

/-- After `j` words of a prime's reduction. -/
structure TrInv (s₀ : State) (B : Addr) (d sp : Nat) (j : Nat) (t : State) : Prop where
  acc : (t.gpr .x2).toNat < 2 * sp
  val : (t.gpr .x2).toNat * 2 ^ (64 * j) % sp = wv s₀.mem B d j % sp
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (d + 8 * j)
  keep : Keep [.x2, .x4, .x5, .x6, .x14, .x16] s₀ t

theorem redc_lo32_toNat (x : BitVec 64) : ((x.setWidth 32 + BitVec.ofNat 32 0).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

/-- One word of `c`: its two halves. -/
theorem trStep_ok {s₀ : State} {B : Addr} {Z d w sp : Nat} (hs : Scr s₀ B Z) (h13 : (s₀.gpr .x13).toNat = sp)
    (h15 : (sp * (s₀.gpr .x15).toNat + 1) % 2 ^ 64 = 0) (hs3 : 3 ≤ sp) (hs13 : sp < 2 ^ 13)
    (hd : d + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : TrInv s₀ B d sp j t) :
    WP isa (.block ((([ld .x5 .x16, .addImm .w .x4 .x5 0] : List Instr) ++ redc32 ++
        ([.lsr .x .x4 .x5 32] : List Instr) ++ redc32 ++ ([next .x16] : List Instr)) ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => TrInv s₀ B d sp (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hs.nowrap
  have t13 : (t.gpr .x13).toNat = sp := by rw [hI.keep.gpr .x13 (by decide)]; exact h13
  have t15 : (sp * (t.gpr .x15).toNat + 1) % 2 ^ 64 = 0 := by rw [hI.keep.gpr .x15 (by decide)]; exact h15
  have hld : InRegions (t.rd ++ t.wr) (off B (d + 8 * j)) 8 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hs.ld (by omega)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x5, .x4] (Q := fun t₁ => t₁.gpr .x5 = word s₀.mem B (d + 8 * j) ∧
      (t₁.gpr .x4).toNat = (word s₀.mem B (d + 8 * j)).toNat % 2 ^ 32 ∧ t₁.mem = t.mem) (by
    brun [exec_addImm_w (show 0 < 4096 by decide), hI.x16, hld, hI.mem]
    exact redc_lo32_toNat _) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h5₁, h4₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redc32_ok (s := sp) (by rw [h4₁]; exact Nat.mod_lt _ (by decide))
    (by rw [k₁.gpr .x2 (by decide)]; exact hI.acc) (by rw [k₁.gpr .x13 (by decide)]; exact t13)
    (by rw [k₁.gpr .x15 (by decide)]; exact t15) hs3 hs13) fun t₂ ⟨⟨hacc₂, hval₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x4] (Q := fun t₃ => (t₃.gpr .x4).toNat = (word s₀.mem B (d + 8 * j)).toNat / 2 ^ 32 ∧
      t₃.mem = t₂.mem) (by
    brun [show t₂.gpr .x5 = word s₀.mem B (d + 8 * j) from (k₂.gpr .x5 (by decide)).trans h5₁]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h4₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have hhi : (word s₀.mem B (d + 8 * j)).toNat / 2 ^ 32 < 2 ^ 32 := by
    have := (word s₀.mem B (d + 8 * j)).isLt; omega
  refine WP.mono (redc32_ok (s := sp) (by rw [h4₃]; exact hhi) (by rw [k₃.gpr .x2 (by decide)]; exact hacc₂)
    (by rw [k₃.gpr .x13 (by decide), k₂.gpr .x13 (by decide), k₁.gpr .x13 (by decide)]; exact t13)
    (by rw [k₃.gpr .x15 (by decide), k₂.gpr .x15 (by decide), k₁.gpr .x15 (by decide)]; exact t15) hs3 hs13)
    fun t₄ ⟨⟨hacc₄, hval₄, hm₄⟩, k₄⟩ => ?_
  have kk := ((k₁.trans k₂).trans k₃).trans k₄
  have h16₄ : t₄.gpr .x16 = off B (d + 8 * j) := (kk.gpr .x16 (by decide)).trans hI.x16
  have h14₄ : t₄.gpr .x14 = t.gpr .x14 := kk.gpr .x14 (by decide)
  refine WP.mono (WP.keep [.x16, .x14] (Q := fun t' => t'.gpr .x16 = off B (d + 8 * (j + 1)) ∧
      t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 ∧ t'.mem = t₄.mem) (by
    brun [h16₄, h14₄]
    rw [Nat.mul_succ, Nat.add_assoc]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h16', h14', hm'⟩, k'⟩ => ⟨⟨by rw [k'.gpr .x2 (by decide)]; exact hacc₄, ?_,
      by rw [hm', hm₄, hm₃, hm₂, hm₁, hI.mem], h16', ((hI.keep.trans kk).trans k').mono (by decide)⟩, h14'⟩
  rw [k'.gpr .x2 (by decide), wv]
  rw [h4₃, show t₃.gpr .x2 = t₂.gpr .x2 from k₃.gpr .x2 (by decide)] at hval₄
  rw [h4₁, show t₁.gpr .x2 = t.gpr .x2 from k₁.gpr .x2 (by decide)] at hval₂
  exact trial_word_math hval₂ hval₄ hI.val

theorem trial_movz_ffff : BitVec.setWidth 64 (0xFFFF : BitVec 16) = (0xFFFF : BitVec 64) := rfl

/-- `x3 := (x17 >>> 16 j) &&& 0xFFFF`. -/
theorem entrySelW_ok (t : State) {X : BitVec 64} (h17 : t.gpr .x17 = X) (j : Nat) (hj : j < 4) :
    WP isa (.block ((if j = 0 then [mov .x3 .x17] else [.lsr .x .x3 .x17 (16 * j)]) ++
      ([.movz .x .x4 0xFFFF 0, .logic .and .x .x3 .x3 .x4] : List Instr))) t fun t' =>
      (t'.gpr .x3 = (X >>> (16 * j)) &&& 0xFFFF ∧ t'.mem = t.mem) ∧ Keep [.x3, .x4] t t' := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel) <;>
    simp only [↓reduceIte, Nat.succ_ne_zero, Nat.mul_zero, BitVec.ushiftRight_zero] <;>
    brun [h17, trial_movz_ffff]

/-- Entry `j` of the table word in `x17` into `x3`. -/
theorem entrySel_ok {t : State} {i j : Nat} (hi : i < 256) (hj : j < 4)
    (h17 : t.gpr .x17 = BitVec.ofNat 64 (tabWord i)) :
    WP isa (.block ((if j = 0 then [mov .x3 .x17] else [.lsr .x .x3 .x17 (16 * j)]) ++
      ([.movz .x .x4 0xFFFF 0, .logic .and .x .x3 .x3 .x4] : List Instr))) t fun t' =>
      ((t'.gpr .x3).toNat = tabEntry (4 * i + j) ∧ t'.mem = t.mem) ∧ Keep [.x3, .x4] t t' :=
  WP.mono (entrySelW_ok t h17 j hj) fun _ ⟨⟨h3, hm⟩, k⟩ => ⟨⟨by rw [h3]; exact tabWord_entry hi hj, hm⟩, k⟩

/-- `subs` of 1 and `csel` of 0 (`x7`) or all ones (`x8`): the mask of zero. -/
theorem trial_zmask (a : BitVec 64) :
    (if decide (2 ^ 64 ≤ a.toNat + (~~~(1#16).setWidth 64 : BitVec 64).toNat + true.toNat) then (0 : BitVec 64)
      else mask true) = mask (decide (a.toNat = 0)) := by
  have e : decide (2 ^ 64 ≤ a.toNat + (~~~(1#16).setWidth 64 : BitVec 64).toNat + true.toNat) =
      !decide (a.toNat = 0) := by
    rw [BitVec.toNat_not, show ((1#16).setWidth 64 : BitVec 64).toNat = 1 from rfl, show true.toNat = 1 from rfl]
    have := a.isLt
    by_cases h : a.toNat = 0 <;> simp [h]; omega
  rw [e]; cases decide (a.toNat = 0) <;> rfl

theorem trial_xor_eq (a b : BitVec 64) : ((a ^^^ b).toNat = 0) ↔ a.toNat = b.toNat := by
  constructor
  · intro h
    have h0 : a ^^^ b = 0 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    rw [BitVec.xor_eq_zero_iff.mp h0]
  · intro h
    rw [BitVec.toNat_inj.mp h, BitVec.xor_self]; rfl

theorem trial_mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> rfl

/-- The mask of `acc ∈ {0, s}`, or'ed into `x1`. -/
theorem entryMask_ok (t : State) (h7 : t.gpr .x7 = 0) (h8 : t.gpr .x8 = mask true) :
    WP isa (.block [movi .x4 1, .subs .x .x3 .x2 .x4, .csel .x .x5 .x7 .x8, .logic .eor .x .x3 .x2 .x13,
      .subs .x .x3 .x3 .x4, .csel .x .x6 .x7 .x8, .logic .orr .x .x5 .x5 .x6, .logic .orr .x .x1 .x1 .x5]) t
      fun t' => (t'.gpr .x1 = t.gpr .x1 ||| mask (decide ((t.gpr .x2).toNat = 0 ∨
        (t.gpr .x2).toNat = (t.gpr .x13).toNat)) ∧ t'.mem = t.mem) ∧ Keep [.x1, .x3, .x4, .x5, .x6] t t' := by
  refine WP.keep [.x1, .x3, .x4, .x5, .x6] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h7, h8, trial_zmask]
  rw [decide_eq_decide.mpr (trial_xor_eq _ _), trial_mask_or, Bool.decide_or]

/-- `trialEntry j`: the mask of `s ∣ c`, for entry `j` of the table word `i`
in `x17`, or'ed into `x1` (`x7 = 0`, `x8` all ones). -/
theorem trialEntry_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i j : Nat} (hi : i < 256) (hj : j < 4)
    (h17 : s.gpr .x17 = BitVec.ofNat 64 (tabWord i)) (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true) :
    WP isa (seqs (trialEntry j)) s fun t =>
      t.gpr .x1 = s.gpr .x1 ||| mask (decide (wv s.mem B (slot w aN) w % tabEntry (4 * i + j) = 0)) ∧
      t.mem = s.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x12, .x13, .x14, .x15, .x16] s t := by
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  obtain ⟨hodd, hs3, hs13'⟩ := tabEntry_facts (i := 4 * i + j) (by omega)
  have hs13 : tabEntry (4 * i + j) < 2 ^ 13 := Nat.lt_of_lt_of_le hs13' (by decide)
  generalize hsp : tabEntry (4 * i + j) = sp at hodd hs3 hs13 ⊢
  unfold trialEntry
  simp only [seqs]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (entrySel_ok hi hj h17) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_
  rw [hsp] at h3₁
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok s₁ (by rw [h3₁]; exact hodd)) fun s₂ ⟨h15₂, k₂, hm₂⟩ => ?_
  rw [h3₁] at h15₂
  have h3₂ : (s₂.gpr .x3).toNat = sp := by rw [k₂.gpr .x3 (by decide)]; exact h3₁
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = s₂.gpr .x3 ∧ t.mem = s₂.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h13₃, hm₃⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  have hm13 : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have h₃ : Ws s₃ B Z w := h.congr' (rs := []) (fun x _ => by rw [hm13]) (by simp) k13 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h₃.ws_ok fun s₄ ⟨⟨h12₄, h11₄, hm₄, _⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aN .x16 ((k₄.gpr .x0 (by decide)).trans h₃.x0) h11₄) fun s₅ ⟨⟨h16₅, hm₅, _⟩, k₅⟩ => ?_
  have h12₅ : s₅.gpr .x12 = BitVec.ofNat 64 w := (k₅.gpr .x12 (by decide)).trans h12₄
  refine WP.mono (WP.keep [.x14, .x2] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x2 = 0 ∧
      t.mem = s₅.mem) (by brun [h12₅]) (by decide) (by decide) (by decide +kernel)) fun s₆ ⟨⟨h14₆, h2₆, hm₆⟩, k₆⟩ => ?_
  have k36 := (k₄.trans k₅).trans k₆
  have hm6 : s₆.mem = s.mem := by rw [hm₆, hm₅, hm₄, hm13]
  have h13₆ : (s₆.gpr .x13).toNat = sp := by rw [k36.gpr .x13 (by decide), h13₃]; exact h3₂
  have h15₆ : (sp * (s₆.gpr .x15).toNat + 1) % 2 ^ 64 = 0 := by
    rw [k36.gpr .x15 (by decide), k₃.gpr .x15 (by decide)]; exact h15₂
  have h16₆ : s₆.gpr .x16 = off B (slot w aN) := (k₆.gpr .x16 (by decide)).trans h16₅
  have hs₆ := h.scr.congr (k13.trans k36).wr
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega) (TrInv s₆ B (slot w aN) sp)
    (fun j' hj' t hI _ => trStep_ok (w := w) hs₆ h13₆ h15₆ hs3 hs13 (by omega) hj' hI)
    ⟨by rw [h2₆]; show 0 < 2 * sp; omega, by rw [h2₆]; simp [wv], rfl,
      by rw [h16₆, Nat.mul_zero, Nat.add_zero], Keep.refl _ _⟩ h14₆) fun s₇ hI => ?_)
  have k17 := ((k13.trans k36).trans hI.keep)
  have hdiv := trial_div hodd hI.acc hI.val
  rw [hm6] at hdiv
  refine WP.mono (entryMask_ok s₇ ((k17.gpr .x7 (by decide)).trans h7) ((k17.gpr .x8 (by decide)).trans h8))
    fun t ⟨⟨h1, hmt⟩, kt⟩ => ⟨?_, by rw [hmt, hI.mem, hm6], (k17.trans kt).mono (by decide)⟩
  rw [h1, k17.gpr .x1 (by decide), (hI.keep.gpr .x13 (by decide)), h13₆]
  exact congrArg _ (congrArg _ (decide_eq_decide.mpr hdiv.symm))

end VG.Proof.RsaKeyGen.AArch64
