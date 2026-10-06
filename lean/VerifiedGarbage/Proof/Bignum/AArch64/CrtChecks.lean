import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut

/-!
# `vg_rsa_private_crt` on AArch64: small pieces of the checks

`zeroArr j` clears array `j` (`zeroArr_ok`), `copyArr o a` copies `[a]` to
`[o]` (`copyArr_ok`), `maskArr j` ands `[j]` with the mask in `sMaskX`
(`maskArr_ok`); `eqCheck` ands into `sMask` the mask of `p q = n`
(`eqCheck_ok`), and `qinvCheck`, in `p`'s workspace, that of `qInv < p`
(`qinvCheck_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Clearing, copying and masking an array -/

/-- `[j] := 0` over `w + 2` words. -/
theorem zeroArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) :
    WP isa (zeroArr j) s fun t => wv t.mem B (slot w j) (w + 2) = 0 ∧
      Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold zeroArr
  refine WP.seq (WP.mono (WP.keep [.x7, .x8, .x12] (Q := fun t => t.gpr .x8 = off B (slot w j) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt hj), hdr_enc (show sW < 32 by decide), hg.ld hZ (sArr_lt hj),
      hg.ld hZ (show sW < 32 by decide), hg.hdr.harr j hj, hg.hdr.hw]) rfl rfl rfl)
    fun s₁ ⟨⟨h8, h12, h7, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroAcc_ok (hg.scr.congr k₁.wr) h8 h12 h7 hw' (Nat.le_trans (slot_le hj) hZ))
    fun t ⟨hv, ho, k⟩ => ⟨hv, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩

/-- `[o] := [a]` over `w` words. -/
theorem copyArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {o a : Nat} (ho : o < 8) (ha : a < 8) (hoa : o ≠ a) :
    WP isa (seqs (copyArr o a)) s fun t => wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧
      Outside B (slot w o) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have so := Nat.le_trans (slot_le (w := w) ho) hZ
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sp := slot_sep (w := w) hoa
  unfold copyArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w o) ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt ho), hdr_enc (show sW < 32 by decide),
      hg.ld hZ (sArr_lt ha), hg.ld hZ (sArr_lt ho), hg.ld hZ (show sW < 32 by decide), hg.hdr.harr a ha,
      hg.hdr.harr o ho, hg.hdr.hw]) rfl rfl rfl) fun s₁ ⟨⟨h12, h16, h17, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.wr
  refine WP.mono (copyWords_ok h16 h17 h12 hw hw' (by omega) (fun i hi => hs₁.ld (by omega))
    (fun i hi => hs₁.st (by omega)) (fun i hi b hb => by rw [ofs_off B (by omega)]; omega))
    fun t ⟨hv, _, ho', _, _, k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho'; exact ho', (k₁.trans k).mono (by decide)⟩

/-- After `j` words of `maskArr`'s loop from `s₀`. -/
structure MaskInv (s₀ : State) (B : Addr) (Z e : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * j)
  out : Outside B e (8 * j) s₀.mem t.mem
  done : ∀ i < j, word t.mem B (e + 8 * i) = word s₀.mem B (e + 8 * i) &&& mask c

theorem maskStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {c : Bool} (h15 : s₀.gpr .x15 = mask c)
    (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : MaskInv s₀ B Z e c j t) :
    WP isa (.block ([ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MaskInv s₀ B Z e c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have hv : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * j)) (word s₀.mem B (e + 8 * j) &&& mask c) ∧
      t₁.gpr .x16 = off B (e + 8 * j + 8))
    (by brun [hI.x16, t15, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega), hv]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc], ?_, fun i hi => ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _

/-- `[j] &= sMaskX` over `w` words. -/
theorem maskArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) {c : Bool}
    (hm : word s.mem B (8 * Crt.sMaskX) = mask c) :
    WP isa (seqs (maskArr j)) s fun t =>
      (∀ i < w, word t.mem B (slot w j + 8 * i) = word s.mem B (slot w j + 8 * i) &&& mask c) ∧
      wv t.mem B (slot w j) w = (if c then wv s.mem B (slot w j) w else 0) ∧
      Outside B (slot w j) (8 * w) s.mem t.mem ∧ t.gpr .x15 = mask c ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have sj := Nat.le_trans (slot_le (w := w) hj) hZ
  unfold maskArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x12, .x14, .x15, .x16] (Q := fun t => t.gpr .x15 = mask c ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w j) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show Crt.sMaskX < 32 by decide), hdr_enc (sArr_lt hj), hdr_enc (show sW < 32 by decide),
      hg.ld hZ (show Crt.sMaskX < 32 by decide), hg.ld hZ (sArr_lt hj), hg.ld hZ (show sW < 32 by decide), hm,
      hg.hdr.harr j hj, hg.hdr.hw]) rfl rfl rfl) fun s₁ ⟨⟨h15, h12, h16, h14, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.wr
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (MaskInv s₁ B Z (slot w j) c)
    (fun i hi t hI _ => maskStep_ok h15 (by omega) hi hI)
    ⟨hs₁, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩ h14)
    fun t hI => ?_
  have hd := hI.done
  have ho := hI.out
  rw [hm₁] at hd ho
  refine ⟨hd, ?_, ho, (hI.keep.gpr .x15 (by decide)).trans h15, (k₁.trans hI.keep).mono (by decide)⟩
  cases c
  · exact (wv_eq_zero_iff _ _ _ _).mpr fun i hi => by rw [hd i hi, mask_false]; exact BitVec.and_zero
  · exact wv_congr fun i hi => by rw [hd i hi, mask_true, BitVec.and_allOnes]

/-! ## `p q = n` -/

/-- Two numbers of `n` words are equal only if their words are. -/
theorem wv_inj {m : Mem} {p : Addr} {d e : Nat} :
    ∀ n, wv m p d n = wv m p e n → ∀ i < n, word m p (d + 8 * i) = word m p (e + 8 * i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [wv] at h
    have hd := wv_lt m p d n
    have he := wv_lt m p e n
    have h1 : wv m p d n = wv m p e n := by
      have := congrArg (· % 2 ^ (64 * n)) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at this
      exact this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact wv_inj n h1 i hi
    · rw [h1] at h
      exact BitVec.eq_of_toNat_eq (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel h))

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := BitVec.or_eq_zero_iff

theorem xor_eq_zero (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b := BitVec.xor_eq_zero_iff

theorem split_eq_iff {L H N R : Nat} (hN : N < R) : L + R * H = N ↔ L = N ∧ H = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨h, rfl⟩
    · have := Nat.le_mul_of_pos_right R hH; omega
  · rintro ⟨rfl, rfl⟩
    rw [Nat.mul_zero, Nat.add_zero]

/-- After `j` words of a loop that ORs words into `x9`, memory unchanged:
`x9 = 0` iff `P j`. -/
structure OrInv (s₀ : State) (B : Addr) (Z : Nat) (P : Nat → Prop) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x9, .x14, .x16, .x17] s₀ t
  mem : t.mem = s₀.mem
  val : t.gpr .x9 = 0 ↔ P j

theorem xorStep_ok {s₀ : State} {B : Addr} {Z w eA eN : Nat} (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State}
    (hI : OrInv s₀ B Z (fun j => ∀ i < j, word s₀.mem B (eA + 8 * i) = word s₀.mem B (eN + 8 * i)) j t)
    (h16 : t.gpr .x16 = off B (eA + 8 * j)) (h17 : t.gpr .x17 = off B (eN + 8 * j)) :
    WP isa (.block ([ld .x3 .x16, ld .x4 .x17, .logic .eor .x .x3 .x3 .x4, .logic .orr .x .x9 .x9 .x3, next .x16,
        next .x17] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => (OrInv s₀ B Z (fun j => ∀ i < j, word s₀.mem B (eA + 8 * i) = word s₀.mem B (eN + 8 * i)) (j + 1) t' ∧
        t'.gpr .x16 = off B (eA + 8 * (j + 1)) ∧ t'.gpr .x17 = off B (eN + 8 * (j + 1))) ∧
        t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x9, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .x9 = t.gpr .x9 ||| (word t.mem B (eA + 8 * j) ^^^ word t.mem B (eN + 8 * j)) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eN + 8 * j + 8))
    (by brun [h16, h17, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h9, h16', h17'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨⟨?_, ?_, ?_⟩, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  · refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), ((hI.keep.trans k₁).trans k').mono (by decide),
      by rw [hm', hm, hI.mem], ?_⟩
    rw [k'.gpr .x9 (by decide), h9, or_eq_zero, xor_eq_zero, hI.val, hI.mem]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      exacts [h1 i hi, h2]
    · intro h
      exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc]
  · rw [k'.gpr .x17 (by decide), h17', Nat.mul_succ, Nat.add_assoc]

theorem orStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop} (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w)
    {t : State} (hI : OrInv s₀ B Z (fun j => A ∧ ∀ i < j, word s₀.mem B (e + 8 * i) = 0) j t)
    (h16 : t.gpr .x16 = off B (e + 8 * j)) :
    WP isa (.block ([ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => (OrInv s₀ B Z (fun j => A ∧ ∀ i < j, word s₀.mem B (e + 8 * i) = 0) (j + 1) t' ∧
        t'.gpr .x16 = off B (e + 8 * (j + 1))) ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x9, .x16] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .x9 = t.gpr .x9 ||| word t.mem B (e + 8 * j) ∧ t₁.gpr .x16 = off B (e + 8 * j + 8))
    (by brun [h16, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h9, h16'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨⟨?_, ?_⟩, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  · refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), ((hI.keep.trans k₁).trans k').mono (by decide),
      by rw [hm', hm, hI.mem], ?_⟩
    rw [k'.gpr .x9 (by decide), h9, or_eq_zero, hI.val, hI.mem]
    constructor
    · rintro ⟨⟨hA, h1⟩, h2⟩
      refine ⟨hA, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      exacts [h1 i hi, h2]
    · rintro ⟨hA, h⟩
      exact ⟨⟨hA, fun i hi => h i (by omega)⟩, h j (by omega)⟩
  · rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc]

/-- `subs` of 1: the carry is set iff the register is not zero. -/
theorem subs_one_c (x : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~(BitVec.setWidth 64 (1#16))).toNat + (true).toNat) = !decide (x = 0) := by
  have h1 : (~~~(BitVec.setWidth 64 (1#16))).toNat = 2 ^ 64 - 2 := by decide
  rw [h1, Bool.toNat_true]
  by_cases hx : x = 0
  · subst hx; decide
  · have : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [hx, decide_false, Bool.not_false, decide_eq_true_eq]
    omega

/-- The mask of `p q = n` (the accumulator's `2 w + 2` words against
`aN`'s `w`), and'ed into `sMask`. -/
theorem eqCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30) :
    WP isa (seqs eqCheck) s fun t =>
      word t.mem B (8 * sMask) = word s.mem B (8 * sMask) &&&
        mask (decide (wv s.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (slot w aN) w)) ∧
      Outside B (8 * sMask) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA : slot w aAcc + 16 * (w + 2) ≤ Z := by
    have := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ; simp only [slot, aTmp, aAcc] at this ⊢; omega
  have hN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hS := hdr_lt_slot w aN (show sMask < 32 by decide)
  unfold eqCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x9, .x12, .x14, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x16 = off B (slot w aAcc) ∧ t.gpr .x17 = off B (slot w aN) ∧ t.gpr .x9 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aAcc < 8 by decide)),
      hdr_enc (sArr_lt (show aN < 8 by decide)), hg.ld hZ (show sW < 32 by decide),
      hg.ld hZ (sArr_lt (show aAcc < 8 by decide)), hg.ld hZ (sArr_lt (show aN < 8 by decide)), hg.hdr.hw,
      hg.hdr.harr aAcc (by decide), hg.hdr.harr aN (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h12, h16, h17, h9, h14, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.wr
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega)
    (fun j t => OrInv s₁ B Z (fun j => ∀ i < j, word s₁.mem B (slot w aAcc + 8 * i) = word s₁.mem B (slot w aN + 8 * i))
      j t ∧ t.gpr .x16 = off B (slot w aAcc + 8 * j) ∧ t.gpr .x17 = off B (slot w aN + 8 * j))
    (fun j hj t hI _ => xorStep_ok (by omega) (by omega) hj hI.1 hI.2.1 hI.2.2)
    ⟨⟨hs₁, Keep.refl _ _, rfl, by rw [h9]; exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩,
      by rw [h16]; rfl, by rw [h17]; rfl⟩ h14) fun s₂ ⟨hI, h16₂, _⟩ => ?_)
  have s₂12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (hI.keep.gpr .x12 (by decide)).trans h12
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (w + 2) ∧ t.mem = s₂.mem)
    (by brun [s₂12, ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨h14₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.wr
  have h16₃ : s₃.gpr .x16 = off B (slot w aAcc + 8 * w) := (k₃.gpr .x16 (by decide)).trans h16₂
  refine WP.seq (WP.mono (wp_countdown (N := w + 2) (by omega) (by omega)
    (fun j t => OrInv s₃ B Z (fun j => (∀ i < w, word s₁.mem B (slot w aAcc + 8 * i) = word s₁.mem B (slot w aN + 8 * i)) ∧
        ∀ i < j, word s₃.mem B (slot w aAcc + 8 * w + 8 * i) = 0) j t ∧
      t.gpr .x16 = off B (slot w aAcc + 8 * w + 8 * j))
    (fun j hj t hI _ => orStep_ok (by omega) hj hI.1 hI.2)
    ⟨⟨hs₃, Keep.refl _ _, rfl, by
      rw [k₃.gpr .x9 (by decide), hI.val]
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩, by rw [h16₃]; rfl⟩ h14₃)
    fun s₄ ⟨hI₂, _⟩ => ?_)
  have hm₄ : s₄.mem = s.mem := hI₂.mem.trans (hm₃.trans (hI.mem.trans hm₁))
  have k14 := ((k₁.trans hI.keep).trans k₃).trans hI₂.keep
  have s₄0 : s₄.gpr .x0 = B := (k14.gpr .x0 (by decide)).trans hg.x0
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (8 * sMask)) (mask (decide (s₄.gpr .x9 = 0)) &&& word s₄.mem B (8 * sMask)))
    (by brun [borrowMask, s₄0, hdr_enc (show sMask < 32 by decide), csel_mask', subs_one_c, Bool.not_not,
      hI₂.scr.ld (show 8 * sMask + 8 ≤ Z by omega), hI₂.scr.st (show 8 * sMask + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₄⟩ => ?_
  have hR : decide (s₄.gpr .x9 = 0) = decide (wv s.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (slot w aN) w) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hI₂.val, hm₃, hI.mem, hm₁,
      show 2 * w + 2 = w + (w + 2) by omega, wv_add, split_eq_iff (wv_lt _ _ _ _), wv_eq_zero_iff]
    exact and_congr ⟨fun h => wv_congr2 h, fun h => wv_inj w h⟩ Iff.rfl
  refine ⟨?_, ?_, (k14.trans k₄).mono (by decide)⟩
  · rw [hm, word_writeW_self, hm₄, BitVec.and_comm, hR]
  · rw [hm, ← hm₄]
    exact writeW_outside _ B _ (by omega)

/-! ## `qInv < p` -/

/-- In a workspace at `off B o` linked to `B`: the mask of `qInv < p`
(`[aChunk] < [aN]`), and'ed into the `sMask` of the workspace at `B`. -/
theorem qinvCheck_ok {s : State} {B : Addr} {Z w o : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = off B o) (hH : Hdr s.mem (off B o) w minv) (hZ : o + slot w 8 ≤ Z)
    (hM : 8 * sMask + 8 ≤ o) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hL : word s.mem (off B o) (8 * Crt.sLink) = B) :
    WP isa (seqs qinvCheck) s fun t =>
      word t.mem B (8 * sMask) = word s.mem B (8 * sMask) &&&
        mask (decide (wv s.mem (off B o) (slot w Crt.aChunk) w < wv s.mem (off B o) (slot w aN) w)) ∧
      Outside B (8 * sMask) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (o + 8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hC := slot_le (w := w) (show Crt.aChunk < 8 by decide)
  have hN := slot_le (w := w) (show aN < 8 by decide)
  have hw0 : word s.mem B (o + 8 * sW) = BitVec.ofNat 64 w := by rw [← word_off]; exact hH.hw
  have ha : ∀ j < 8, word s.mem B (o + 8 * sArr j) = off B (o + slot w j) := fun j hj => by
    rw [← word_off, hH.harr j hj, off_off]
  unfold qinvCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x16 = off B (o + slot w Crt.aChunk) ∧ t.gpr .x17 = off B (o + slot w aN) ∧
      t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show Crt.aChunk < 8 by decide)),
      hdr_enc (sArr_lt (show aN < 8 by decide)), hl sW (by decide), hl _ (sArr_lt (show Crt.aChunk < 8 by decide)),
      hl _ (sArr_lt (show aN < 8 by decide)), hw0, ha Crt.aChunk (by decide), ha aN (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h12, h16, h17, h7, h14, hc, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hs.congr k₁.wr) h16 h17 h14 hc hw hw' (by omega) (by omega))
    fun s₂ ⟨hc₂, hm₂, k₂⟩ => ?_)
  rw [hm₁, ← wv_off, ← wv_off] at hc₂
  have k12 := k₁.trans k₂
  have s₂0 : s₂.gpr .x0 = off B o := (k12.gpr .x0 (by decide)).trans h0
  have s₂7 : s₂.gpr .x7 = 0 := (k₂.gpr .x7 (by decide)).trans h7
  have hs₂ := hs.congr k12.wr
  have hL₂ : word s₂.mem B (o + 8 * Crt.sLink) = B := by rw [hm₂, hm₁, ← word_off]; exact hL
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x15] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (8 * sMask)) (mask (!s₂.c) &&& word s₂.mem B (8 * sMask)))
    (by brun [borrowMask, ldw, stw, s₂0, s₂7, csel_mask', hdr_enc (show Crt.sLink < 32 by decide),
      hdr_enc (show sMask < 32 by decide), hs₂.ld (d := o + 8 * Crt.sLink) (by
        have := hdr_lt_slot w 8 (show Crt.sLink < 32 by decide); omega), hL₂,
      hs₂.ld (show 8 * sMask + 8 ≤ Z by omega), hs₂.st (show 8 * sMask + 8 ≤ Z by omega)]; cases s₂.c <;> rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  refine ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm, word_writeW_self, hc₂, Bool.not_not, hm₂, hm₁, BitVec.and_comm]
  · rw [hm, hm₂, hm₁]; exact writeW_outside _ B _ (by omega)

end VG.Proof.Bignum.AArch64
