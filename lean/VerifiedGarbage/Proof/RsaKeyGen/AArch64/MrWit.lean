import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrCtx
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub

/-!
# A candidate on AArch64: Miller–Rabin's witness

`witLoad_ok`: the next `8 w` octets of `rand` into `aX`, `kUsed` advanced;
`witLow_ok`: `x5` zero iff `x ≤ 1`; `witCmp_ok`: the masks of `x ≥ 2` and
`(x | 1) < c`; `witForce_ok`: the witness forced into range unless both
hold.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX)

/-- The witness's octets into `aX`. -/
theorem witLoad_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rp : Addr} {u : Nat} {bs : List Byte}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z (rp + BitVec.ofNat 64 u) bs) (hbl : bs.length = 8 * w) :
    WP isa (seqs [zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
        ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE]) s fun t =>
      wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧ word t.mem B (8 * kUsed) = BitVec.ofNat 64 (u + 8 * w) ∧
      Frm B [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧ Ws t B Z w ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have sj := h.sl (show aX < 16 by decide)
  have hw2 := h.w2
  have hw1 := h.w1
  have hUs : 8 * kUsed + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h (show aX < 16 by decide)) fun s₁ ⟨_, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w aX _) k₁ (by decide)
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w aX hi; omega_using [this])) (by omega_using [hi])
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok aX .x8 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x3, .x2] (Q := fun t => t.gpr .x1 = rp + BitVec.ofNat 64 u ∧
        t.gpr .x2 = BitVec.ofNat 64 (8 * w) ∧
        t.mem = s₃.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (u + 8 * w))) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h₁.x0
          have hs₃ := h₁.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_using [hi, this])
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by omega_using [sj, hUs]), hh kRand (by decide),
            hh kUsed (by decide), hh kLen (by decide), hR, hU, hK, BitVec.ofNat_add])
        (by decide) (by decide) (by decide +kernel))
      fun s₄ ⟨⟨h1, h2, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.wr
  have hm₃ : s₃.mem = s₁.mem := m₃.trans m₂
  have oU : Outside B (8 * kUsed) 8 s₁.mem s₄.mem := by rw [m₄, hm₃]; exact writeW_outside _ _ _ (by omega_using [hn, sj, hUs])
  have hsrc₄ : Src s₄ B Z (rp + BitVec.ofNat 64 u) bs := hsrc.congrK (fun x hx => by
    rw [oU x (Or.inr (by omega_using [sj, hUs, hx])), o₁ x (Or.inr (by omega_using [sj, hx]))]) k14
  have hw8 : (8 * w + 7) / 8 = w := by omega_using []
  refine WP.mono (loadBE_ok (w := (8 * w + 7) / 8) hs₄ h1 h2 ((k₄.gpr .x8 (by decide)).trans h8) hbl (by omega_using [hw1])
    (by omega_using [hw2]) rfl (by rw [hw8]; omega_using [sj]) (fun i hi => hsrc₄.rd i (by omega_using [hbl, hi]))
        (fun i hi => hsrc₄.val i (by omega_using [hbl, hi]))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega_using [hbl, hi]); rw [hw8]; omega_using [sj, this]))) fun t ⟨hv, o, k₅⟩ => ?_
  rw [hw8] at hv o
  have F : Frm B [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem :=
    ((Frm.of_outside o₁ (by simp)).trans (Frm.of_outside oU (by simp))).trans
      (Frm.of_outside (o.mono (o' := slot w aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp))
  refine ⟨hv, ?_, F, h.congr' F (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact KMut.ofSlot w _ _
      · exact KMut.hdr (by simp [kUsed, sFn, sW, sStride, sArr])) (k14.trans k₅) (by decide),
    (k14.trans k₅).mono (by decide)⟩
  rw [o.word (Or.inl (by omega_using [hUs])) (by omega_using [hn, sj, hUs]), m₄, word_writeW_self]

theorem lsr1_eq_zero (x : BitVec 64) : x >>> 1 = 0 ↔ x &&& (BitVec.allOnes 64 - 1) = 0 := by
  rw [and_m2_eq_zero]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    rw [Nat.pow_one, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega_using [this]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.pow_one, show (0 : BitVec 64).toNat = 0 from rfl]
    omega_using [h]

/-- After `j + 1` words of a loop that ORs words `1, 2, …` into `x5`. -/
structure OrInv (s₀ : State) (B : Addr) (Z e : Nat) (A : Prop) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x5, .x14, .x16] s₀ t
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (e + 8 * (j + 1))
  val : t.gpr .x5 = 0 ↔ (A ∧ ∀ i, 1 ≤ i → i < j + 1 → word s₀.mem B (e + 8 * i) = 0)

theorem orStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop} (he : e + 8 * w ≤ Z) {j : Nat}
    (hj : j + 1 < w) {t : State} (hI : OrInv s₀ B Z e A j t) :
    WP isa (.block ([ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => OrInv s₀ B Z e A (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x5, .x16] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .x5 = t.gpr .x5 ||| word t.mem B (e + 8 * (j + 1)) ∧ t₁.gpr .x16 = off B (e + 8 * (j + 1) + 8))
    (by brun [hI.x16, hI.scr.ld (show e + 8 * (j + 1) + 8 ≤ Z by omega_using [he, hj])]) (by decide) (by decide)
    (by decide +kernel)) fun t₁ ⟨⟨hm, h5, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], by rw [k'.gpr .x16 (by decide), h16, show e + 8 * (j + 1) + 8 = e + 8 * (j + 1 + 1) by omega_using []],
    ?_⟩
  rw [k'.gpr .x5 (by decide), h5, VG.Proof.Rsa.AArch64.or_eq_zero, hI.val, hI.mem]
  constructor
  · rintro ⟨⟨hA, h1⟩, h2⟩
    refine ⟨hA, fun i hi1 hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi1 hi, h2]
  · rintro ⟨hA, h⟩
    exact ⟨⟨hA, fun i hi1 hi => h i hi1 (by omega_using [hi])⟩, h (j + 1) (by omega_using []) (by omega_using [])⟩

/-- `x5` zero iff `x ≤ 1`, for `x` in `aX`. -/
theorem witLow_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16,
        .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]]) s fun t =>
      (t.gpr .x5 = 0 ↔ wv s.mem B (slot w aX) w ≤ 1) ∧ t.mem = s.mem ∧
      Keep [.x11, .x12, .x16, .x5, .x14, .x3] s t := by
  have hn := h.scr.nowrap
  have sX := h.sl (show aX < 16 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ =>
    WP.mono (base_ok aX .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ =>
      WP.mono (WP.keep [.x5, .x16, .x14] (Q := fun t => t.gpr .x5 = word s.mem B (slot w aX) >>> 1 ∧
        t.gpr .x16 = off B (slot w aX + 8 * (0 + 1)) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s₂.mem) (by
          have hs₂ := h.scr.congr (k₁.trans k₂).wr
          brun [h16, (k₂.gpr .x12 (by decide)).trans h12, m₂, m₁, hs₂.ld (d := slot w aX) (by omega_using [sX]), off_add,
            ofNat_sub_one' (p := w) (by omega_using [hw1]) (by omega_using [hw2])])
        (by decide) (by decide) (by decide +kernel))
      fun s₃ ⟨⟨h5, h16₃, h14, m₃⟩, k₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  have hm3 : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  refine WP.mono (wp_countdown (N := w - 1) (by omega_using [hw2]) (by omega_using [hw1])
    (fun j t => OrInv s₃ B Z (slot w aX) (word s.mem B (slot w aX) >>> 1 = 0) j t)
    (fun j hj t hI _ => orStep_ok (w := w) (by omega_using [sX]) (by omega_using [hj]) hI)
    ⟨h.scr.congr k13.wr, Keep.refl _ _, rfl, h16₃, by
      rw [h5]; exact ⟨fun h => ⟨h, fun i h1 h2 => absurd h2 (by omega_using [h1])⟩, fun h => h.1⟩⟩ h14)
    fun t hI => ?_
  refine ⟨?_, by rw [hI.mem, hm3], (k13.trans hI.keep).mono (by decide)⟩
  rw [hI.val, hm3, wv_le_one (by omega_using [hw1]), lsr1_eq_zero, show w - 1 + 1 = w by omega_using [hw1]]

/-- The mask of `x ≥ 2` from `x5`: `x7 := 0`, `x8` all ones, `x4 := 1`. -/
theorem witGe2_ok (s : State) {X : Nat} (hlow : s.gpr .x5 = 0 ↔ X ≤ 1) :
    WP isa (.block [movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7]) s
      fun t => (t.gpr .x9 = mask (decide (2 ≤ X)) ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧ t.gpr .x4 = 1 ∧
        t.mem = s.mem) ∧ Keep [.x7, .x8, .x4, .x3, .x9] s t := by
  refine WP.keep [.x7, .x8, .x4, .x3, .x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [subs_carry]
  have e : decide ((BitVec.setWidth 64 1#16).toNat ≤ (s.gpr .x5).toNat) = decide (2 ≤ X) := by
    rw [show (BitVec.setWidth 64 1#16).toNat = 1 from rfl]
    refine decide_eq_decide.mpr ⟨fun h1 => ?_, fun h2 => ?_⟩
    · by_contra hx
      rw [hlow.mpr (by omega_using [hx])] at h1
      exact absurd h1 (by decide)
    · by_contra hx
      exact absurd (hlow.mp (BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_using [hx])))
        (by omega_using [h2])
  rw [e]
  cases decide (2 ≤ X) <;> rfl

theorem or1_toNat (x : BitVec 64) : (x ||| 1).toNat = x.toNat + (1 - x.toNat % 2) := by
  rw [BitVec.toNat_or, show (1 : BitVec 64).toNat = 1 from rfl]
  have h1 : (x.toNat ||| 1) / 2 = x.toNat / 2 := by
    have := Nat.or_div_two_pow (a := x.toNat) (b := 1) (n := 1); simpa using this
  have h2 : (x.toNat ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega_using [h1, h2]

/-- The low words: `(x₀ | 1) − c₀`, its borrow in the carry flag. -/
theorem witCmpLow_ok {s : State} {B : Addr} {Z w eX eN : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eX)
    (h17 : s.gpr .x17 = off B eN) (h4 : s.gpr .x4 = 1) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hX : eX + 8 ≤ Z) (hN : eN + 8 ≤ Z) :
    WP isa (.block [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4, next .x16,
      next .x17, .subImm .x .x14 .x12 1]) s fun t =>
      ((∃ d : Nat, d < 2 ^ (64 * 1) ∧ d + (word s.mem B eN).toNat =
          (word s.mem B eX).toNat + (1 - (word s.mem B eX).toNat % 2) + 2 ^ (64 * 1) * (!t.c).toNat) ∧
        t.gpr .x16 = off B (eX + 8 * 1) ∧ t.gpr .x17 = off B (eN + 8 * 1) ∧
        t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x16, .x17, .x14] s t := by
  have hn := hs.nowrap
  refine WP.keep [.x3, .x4, .x16, .x17, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h16, h17, h4, h12, hs.ld (d := eX) (by omega_using [hX]), hs.ld (d := eN) (by omega_using [hN]), off_add,
    ofNat_sub_one' (p := w) (by omega_using [hw]) (by omega_using [hw'])]
  have e := sbcs_toNat (s.mem.readW (off B eX) 64 ||| 1) (s.mem.readW (off B eN) 64) true
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e
  have e2 := or1_toNat (s.mem.readW (off B eX) 64)
  rw [Nat.mul_one]
  exact ⟨_, BitVec.isLt ((s.mem.readW (off B eX) 64 ||| 1) + ~~~s.mem.readW (off B eN) 64 +
    BitVec.ofNat 64 true.toNat), by unfold word; omega_using [e, e2]⟩

/-- After `j` words of the comparison of `X + δ` with `N`. -/
structure CmpInvD (s₀ : State) (B : Addr) (Z eX eN δ : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eN + 8 * j)
  val : ∃ d : Nat, d < 2 ^ (64 * j) ∧
    d + wv s₀.mem B eN j = wv s₀.mem B eX j + δ + 2 ^ (64 * j) * (!t.c).toNat

theorem cmpStepD_ok {s₀ : State} {B : Addr} {Z w eX eN δ : Nat} (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : CmpInvD s₀ B Z eX eN δ j t) :
    WP isa (.block ([ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => CmpInvD s₀ B Z eX eN δ (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  obtain ⟨d, hd, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j)).toNat + (~~~word t.mem B (eN + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x3 = word t.mem B (eX + 8 * j) + ~~~word t.mem B (eN + 8 * j) + BitVec.ofNat 64 t.c.toNat ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eN + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_using [hN, hj])]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, hc, h3, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hs := sbcs_toNat (word t.mem B (eX + 8 * j)) (word t.mem B (eN + 8 * j)) t.c
  rw [hI.mem] at hs
  generalize (word s₀.mem B (eX + 8 * j) + ~~~word s₀.mem B (eN + 8 * j) + BitVec.ofNat 64 t.c.toNat) = r at hs
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ⟨d + 2 ^ (64 * j) * r.toNat, ?_, ?_⟩⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * j)) (show r.toNat + 1 ≤ 2 ^ 64 from r.isLt)
    rw [pow64_succ]; rw [Nat.mul_add, Nat.mul_one] at this; omega_using [hd, this]
  · rw [hc', hc, hI.mem]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `witCmp_ok`'s head: the mask of `x ≥ 2` and the low words compared. -/
theorem witCmpHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {X : Nat}
    (hlow : s.gpr .x5 = 0 ↔ X ≤ 1) :
    WP isa (.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4,
        .csel .x .x9 .x8 .x7] ++ ws ++ base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4,
        ld .x4 .x17, .subs .x .x3 .x3 .x4, next .x16, next .x17, .subImm .x .x14 .x12 1])) s fun t =>
      (t.gpr .x9 = mask (decide (2 ≤ X)) ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        t.gpr .x16 = off B (slot w aX + 8 * 1) ∧ t.gpr .x17 = off B (slot w aN + 8 * 1) ∧
        t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧
        ∃ d : Nat, d < 2 ^ (64 * 1) ∧ d + (word s.mem B (slot w aN)).toNat =
          (word s.mem B (slot w aX)).toNat + (1 - (word s.mem B (slot w aX)).toNat % 2) +
            2 ^ (64 * 1) * (!t.c).toNat) ∧
      Keep [.x7, .x8, .x4, .x3, .x9, .x11, .x12, .x16, .x17, .x14] s t := by
  have hn := h.scr.nowrap
  have sX := h.sl (show aX < 16 by decide)
  have sN := h.sl (show aN < 16 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (witGe2_ok s hlow) fun s₁ ⟨⟨h9, h7, h8, h4, m₁⟩, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr' (rs := []) (fun x _ => by rw [m₁]) (by simp) k₁ (by decide)
  refine WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aX .x16 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11)
    fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aN .x17 (((k₂.trans k₃).gpr .x0 (by decide)).trans h₁.x0)
    ((k₃.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h17, m₄, _⟩, k₄⟩ => ?_)
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hm₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have k24 := (k₂.trans k₃).trans k₄
  refine WP.mono (witCmpLow_ok (w := w) (h.scr.congr k14.wr) ((k₄.gpr .x16 (by decide)).trans h16) h17
    ((k24.gpr .x4 (by decide)).trans h4) ((k₃.trans k₄).gpr .x12 (by decide) |>.trans h12) (by omega_using [hw1]) (by omega_using [hw2])
    (by omega_using [sX]) (by omega_using [sN])) fun t ⟨⟨hd, h16', h17', h14', hm⟩, k₅⟩ => ?_
  have k25 := k24.trans k₅
  rw [hm₄] at hd
  exact ⟨⟨(k25.gpr .x9 (by decide)).trans h9, (k25.gpr .x7 (by decide)).trans h7,
    (k25.gpr .x8 (by decide)).trans h8, ((k₃.trans k₄).trans k₅ |>.gpr .x12 (by decide)).trans h12,
    ((k₃.trans k₄).trans k₅ |>.gpr .x11 (by decide)).trans h11, hm.trans hm₄, h16', h17', h14', hd⟩,
    (k14.trans k₅).mono (by decide)⟩

/-- The masks of `x ≥ 2` (`x9`) and, in the carry flag, of `(x | 1) ≥ c`. -/
theorem witCmp_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {X : Nat}
    (hX : wv s.mem B (slot w aX) w = X) (hlow : s.gpr .x5 = 0 ↔ X ≤ 1) :
    WP isa (seqs [.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4,
        .csel .x .x9 .x8 .x7] ++ ws ++ base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4,
        ld .x4 .x17, .subs .x .x3 .x3 .x4, next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop]) s fun t =>
      t.gpr .x9 = mask (decide (2 ≤ X)) ∧ t.c = !decide (X + (1 - X % 2) < wv s.mem B (slot w aN) w) ∧
      t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
      Keep [.x7, .x8, .x4, .x3, .x9, .x11, .x12, .x16, .x17, .x14] s t := by
  have hn := h.scr.nowrap
  have sX := h.sl (show aX < 16 by decide)
  have sN := h.sl (show aN < 16 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  have hx2 : X % 2 = (word s.mem B (slot w aX)).toNat % 2 := by
    have e := wv_add s.mem B (slot w aX) 1 (w - 1)
    rw [show 1 + (w - 1) = w by omega_using [hw1], hX] at e
    have : wv s.mem B (slot w aX) 1 = (word s.mem B (slot w aX)).toNat := by simp [wv]
    rw [this] at e
    have : 2 ^ (64 * 1) * wv s.mem B (slot w aX + 8 * 1) (w - 1) % 2 = 0 := by rw [Nat.mul_mod]; simp
    omega_using [e]
  simp only [seqs]
  refine WP.seq (WP.mono (witCmpHead_ok h hlow)
    fun s₁ ⟨⟨h9, h7, h8, h12, h11, m₁, h16, h17, h14, d, hd, hval⟩, k₁⟩ => ?_)
  have hv1 : ∀ e, wv s₁.mem B e 1 = (word s.mem B e).toNat := fun e => by rw [m₁]; simp [wv]
  unfold cmpLoop
  refine WP.mono (wp_countdown (N := w - 1) (by omega_using [hw2]) (by omega_using [hw1])
    (fun i t => CmpInvD s₁ B Z (slot w aX) (slot w aN) (1 - X % 2) (i + 1) t)
    (fun i hi t hI _ => cmpStepD_ok (w := w) (by omega_using [sX]) (by omega_using [sN]) (by omega_using [hi]) hI)
    ⟨h.scr.congr k₁.wr, Keep.refl _ _, rfl, h16, h17, ⟨d, hd, by rw [hv1, hv1, hx2]; exact hval⟩⟩ h14)
    fun t hI => ?_
  obtain ⟨d', hd', hval'⟩ := hI.val
  rw [show w - 1 + 1 = w by omega_using [hw1], m₁, hX] at hval'
  rw [show w - 1 + 1 = w by omega_using [hw1]] at hd'
  have k := k₁.trans hI.keep
  refine ⟨(hI.keep.gpr .x9 (by decide)).trans h9, ?_, (hI.keep.gpr .x7 (by decide)).trans h7,
    (hI.keep.gpr .x8 (by decide)).trans h8, (hI.keep.gpr .x12 (by decide)).trans h12,
    (hI.keep.gpr .x11 (by decide)).trans h11, hI.mem.trans m₁, k.mono (by decide)⟩
  have := lt_of_borrow (X := X + (1 - X % 2)) hd' (by rw [hval'])
  rw [← this, Bool.not_not]

theorem force_lo (x : BitVec 64) (u : Bool) :
    (x ||| BitVec.setWidth 64 2#16 &&& mask (!u)) = if u = true then x else x ||| 2 := by
  cases u
  · simp only [Bool.not_false, mask_true, BitVec.and_allOnes, Bool.false_eq_true, ↓reduceIte]; rfl
  · rw [Bool.not_true, mask_false]; simp

theorem force_hi (x V : BitVec 64) (u : Bool) :
    x &&& (V &&& mask (!u) ^^^ mask true) = if u = true then x else x &&& ~~~V := by
  cases u
  · simp only [Bool.not_false, mask_true, BitVec.and_allOnes, BitVec.xor_allOnes, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.not_true, mask_false, mask_true, ↓reduceIte]
    rw [show V &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show (0 : BitVec 64) ^^^ BitVec.allOnes 64 = BitVec.allOnes 64 from BitVec.zero_xor, BitVec.and_allOnes]

/-- The witness forced into range unless `u = a ∧ b` (the mask `a` in `x9`,
and `b` the carry clear), and the mask of `u` into `kU`. -/
theorem witForce_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {a b : Bool}
    (h9 : s.gpr .x9 = mask a) (hc : s.c = !b) (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (([.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15, sth .x9 kU, .logic .eor .x .x9 .x9 .x8] : List Instr) ++
      base aX .x16 ++ [movi .x4 2, .logic .and .x .x4 .x4 .x9, ld .x3 .x16, .logic .orr .x .x3 .x3 .x4,
      st .x3 .x16, .lsl .x .x5 .x12 3, .add .x .x16 .x16 .x5, .subImm .x .x16 .x16 8, .movz .x .x4 0x8000 3,
      .logic .and .x .x4 .x4 .x9, .logic .eor .x .x4 .x4 .x8, ld .x3 .x16, .logic .and .x .x3 .x3 .x4,
      st .x3 .x16])) s fun t =>
      t.mem = ((s.mem.writeW (off B (8 * kU)) (mask (a && b))).writeW (off B (slot w aX))
        (if a && b then word s.mem B (slot w aX) else word s.mem B (slot w aX) ||| 2)).writeW
        (off B (slot w aX + 8 * (w - 1)))
        (if a && b then word s.mem B (slot w aX + 8 * (w - 1))
          else word s.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63))) ∧
      Keep [.x15, .x9, .x16, .x4, .x3, .x5] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have sX := h.sl (show aX < 16 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  have hU : 8 * kU + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x15, .x9] (Q := fun t => t.gpr .x9 = mask (!(a && b)) ∧ t.gpr .x8 = mask true ∧
      t.mem = s.mem.writeW (off B (8 * kU)) (mask (a && b))) (by
    brun [h9, hc, h7, h8, h.x0, hdr_enc (show kU < 32 by decide), hs.st (d := 8 * kU) (by omega_using [sX, hU])]
    cases a <;> cases b <;> exact ⟨by decide, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h9₁, h8₁, m₁⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aX .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) ((k₁.gpr .x11 (by decide)).trans h11))
    fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hm₂ : s₂.mem = s.mem.writeW (off B (8 * kU)) (mask (a && b)) := m₂.trans m₁
  refine WP.mono (WP.keep [.x4, .x3, .x5, .x16] (Q := fun t => t.mem = ((s.mem.writeW (off B (8 * kU))
      (mask (a && b))).writeW (off B (slot w aX))
        (if a && b then word s.mem B (slot w aX) else word s.mem B (slot w aX) ||| 2)).writeW
        (off B (slot w aX + 8 * (w - 1)))
        (if a && b then word s.mem B (slot w aX + 8 * (w - 1))
          else word s.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)))) (by
    brun [hm₂, h16, (k₂.gpr .x9 (by decide)).trans h9₁, (k₂.gpr .x8 (by decide)).trans h8₁,
      (k12.gpr .x12 (by decide)).trans h12, exec_movz_x' (show 3 < 4 by decide),
      top_addr B (d := slot w aX) (w := w) (by omega_using [hw1]) (by omega_using [hw2]),
      hs₂.ld (d := slot w aX) (by omega_using [sX]), hs₂.st (d := slot w aX) (by omega_using [sX]),
      hs₂.ld (d := slot w aX + 8 * (w - 1)) (by omega_using [sX]), hs₂.st (d := slot w aX + 8 * (w - 1)) (by omega_using [sX]),
      fun X => (writeW_outside s.mem B X (d := 8 * kU) (by omega_using [hn, sX, hU])).word (d := slot w aX) (Or.inr hU)
          (by omega_using [hn, sX]),
      fun X Y => ((writeW_outside _ B Y (d := slot w aX) (by omega_using [hn, sX])).word (d := slot w aX + 8 * (w - 1))
        (Or.inr (by omega_using [hw1])) (by omega_using [hn, sX])).trans
        ((writeW_outside s.mem B X (d := 8 * kU) (by omega_using [hn, sX, hU])).word (d := slot w aX + 8 * (w - 1))
        (Or.inr (by omega_using [hU])) (by omega_using [hn, sX]))]
    rw [force_lo, force_hi, show (BitVec.setWidth 64 (32768 : BitVec 16) <<< (16 * 3) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 63) from by decide]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ⟨hm, (k12.trans k₃).mono (by decide)⟩

/-- Setting bit 1 of the low word and clearing the top bit of the top word
of a number of `w ≥ 2` words. -/
theorem wv_force {m m' : Mem} {p : Addr} {d w : Nat} (hw : 2 ≤ w)
    (h0 : word m' p d = word m p d ||| 2)
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)))
    (hmid : ∀ j, 0 < j → j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = (wv m p d w ||| 2) % 2 ^ (64 * w - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
  have h2 : ∀ j, Nat.testBit 2 j = decide (j = 1) := fun j => by
    rcases j with _ | _ | j
    · rfl
    · rfl
    · rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]; simp
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi, testBit_wv m p d w i hi]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, h0, BitVec.toNat_or, Nat.testBit_or,
        show (2 : BitVec 64).toNat = 2 from rfl, h2, h2, show i % 64 = i by omega_using [hj0],
        decide_eq_true (show i < 64 * w - 1 by omega_using [hw, hj0])]
      simp
    · by_cases hjt : i / 64 = w - 1
      · rw [hjt, htop, BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_not, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 2 ^ 63 < 2 ^ 64 by decide), h2, decide_eq_false (show ¬ i = 1 by omega_using [hj0])]
        rw [show 2 ^ 64 - 1 - 2 ^ 63 = 2 ^ 63 - 1 by decide, Nat.testBit_two_pow_sub_one]
        by_cases hm : i % 64 < 63
        · simp [hm, show i < 64 * w - 1 by omega_using [hj0, hjt, hm]]
        · simp [hm, show ¬ i < 64 * w - 1 by omega_using [hjt, hm]]
      · rw [hmid (i / 64) (by omega_using [hj0]) (by omega_using [hi, hjt]), h2, decide_eq_false (show ¬ i = 1 by omega_using [hj0]),
          decide_eq_true (show i < 64 * w - 1 by omega_using [hi, hjt])]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega_using [hi]))),
      decide_eq_false (show ¬ i < 64 * w - 1 by omega_using [hi])]
    simp

/-- What `mrWitness` changes. -/
def witRanges (w : Nat) : List (Nat × Nat) := [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8), (8 * kU, 8)]

theorem witRanges_mut (w : Nat) : ∀ r ∈ witRanges w, KMut r := by
  simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact KMut.ofSlot w _ _
  · exact KMut.hdr (by simp [kUsed, sFn, sW, sStride, sArr])
  · exact KMut.hdr (by simp [kU, sW])

/-- `MrCtx` across changes in `witRanges`. -/
theorem MrCtx.of_wit {s t : State} {B : Addr} {Z w c bm : Nat} (hc : MrCtx s B Z w c bm)
    (hf : Frm B (witRanges w) s.mem t.mem) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) :
    MrCtx t B Z w c bm := by
  refine hc.of_frm hf (witRanges_mut w) k hr ?_ ?_ ?_ ?_ ?_ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, witRanges, slot,
      hdrBytes, aN, aX, aB, aR1, aRm1, kUsed, kU, sFn, sMinv]
    and_intros <;> omega_using []

theorem mrWitness_eq : mrWitness =
    ([zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
        ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE] : List (Prog isa)) ++
    (([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]] : List (Prog isa)) ++
    (([.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4,
        .csel .x .x9 .x8 .x7] ++ ws ++ base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4,
        ld .x4 .x17, .subs .x .x3 .x3 .x4, next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop]
        : List (Prog isa)) ++
    ([.block (([.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15, sth .x9 kU, .logic .eor .x .x9 .x9 .x8] : List Instr) ++
      base aX .x16 ++ [movi .x4 2, .logic .and .x .x4 .x4 .x9, ld .x3 .x16, .logic .orr .x .x3 .x3 .x4,
      st .x3 .x16, .lsl .x .x5 .x12 3, .add .x .x16 .x16 .x5, .subImm .x .x16 .x16 8, .movz .x .x4 0x8000 3,
      .logic .and .x .x4 .x4 .x9, .logic .eor .x .x4 .x4 .x8, ld .x3 .x16, .logic .and .x .x3 .x3 .x4,
      st .x3 .x16])] : List (Prog isa)))) := rfl

/-- `mrWitness`: the witness `Spec.RsaKeyGen.witness (c − 1) x` for the next
`8 w` octets `x` of `rand` in `aX`, the mask of its uniformity in `kU`, and
`kUsed` advanced. -/
theorem mrWitness_ok {s : State} {B : Addr} {Z w c bm : Nat} (hc : MrCtx s B Z w c bm) (hw4 : 4 ≤ w)
    (_hw64 : w ≤ 64) (hodd : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {u : Nat} {bs : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z (rp + BitVec.ofNat 64 u) bs) (hbl : bs.length = 8 * w) :
    WP isa (seqs mrWitness) s fun t => MrCtx t B Z w c bm ∧
      wv t.mem B (slot w aX) w = (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip bs)).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (u + 8 * w) ∧
      Frm B (witRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have h := hc.ws
  have hn := h.scr.nowrap
  have hw2 := h.w2
  have sX := h.sl (show aX < 16 by decide)
  have hU8 : 8 * kU + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  have hUs8 : 8 * kUsed + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  rw [mrWitness_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witLoad_ok h hR hU hK hsrc hbl) fun s₁ ⟨hx₁, hu₁, hf₁, h₁, k₁⟩ => ?_
  have hf₁' : Frm B (witRanges w) s.mem s₁.mem := hf₁.mono (by simp [witRanges])
  have hc₁ : MrCtx s₁ B Z w c bm := hc.of_wit hf₁' k₁ (by decide)
  have hx : Spec.Rsa.os2ip bs < 2 ^ (64 * w) := by
    have := os2ip_lt bs; rw [hbl, pow256_eq] at this; rwa [show 8 * (8 * w) = 64 * w by omega_using []] at this
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witLow_ok h₁) fun s₂ ⟨hlow, hm₂, k₂⟩ => ?_
  have h₂ : Ws s₂ B Z w := h₁.congr' (rs := []) (fun x _ => by rw [hm₂]) (by simp) k₂ (by decide)
  rw [hx₁] at hlow
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witCmp_ok h₂ (X := Spec.Rsa.os2ip bs) (by rw [hm₂, hx₁]) hlow)
    fun s₃ ⟨h9, hc₃, h7, h8, h12, h11, hm₃, k₃⟩ => ?_
  rw [hm₂, hc₁.n] at hc₃
  have h₃ : Ws s₃ B Z w := h₂.congr' (rs := []) (fun x _ => by rw [hm₃]) (by simp) k₃ (by decide)
  simp only [seqs]
  refine WP.mono (witForce_ok h₃ h9 hc₃ h7 h8 h12 h11) fun t ⟨hm, k⟩ => ?_
  rw [hm₃, hm₂] at hm
  generalize hu : (decide (2 ≤ Spec.Rsa.os2ip bs) &&
    decide (Spec.Rsa.os2ip bs + (1 - Spec.Rsa.os2ip bs % 2) < c)) = uu at hm
  have hwit := witness_eq hodd hb hx
  rw [hu] at hwit
  -- The words of `aX` after the stores.
  have hw0 : word t.mem B (slot w aX) = if uu then word s₁.mem B (slot w aX) else word s₁.mem B (slot w aX) ||| 2 := by
    rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_using [hn, sX])).word (d := slot w aX)
        (Or.inl (by omega_using [hw4]))
      (by omega_using [hn, sX]), word_writeW_self]
  have hwt : word t.mem B (slot w aX + 8 * (w - 1)) = if uu then word s₁.mem B (slot w aX + 8 * (w - 1))
      else word s₁.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)) := by
    rw [hm, word_writeW_self]
  have hwm : ∀ j, 0 < j → j < w - 1 → word t.mem B (slot w aX + 8 * j) = word s₁.mem B (slot w aX + 8 * j) := by
    intro j hj0 hj
    rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_using [hn, sX])).word (Or.inl
        (by omega_using [hj])) (by omega_using [hn, sX, hj]),
      (writeW_outside _ B _ (d := slot w aX) (by omega_using [hn, sX])).word (Or.inr (by omega_using [hj0])) (by omega_using [hn, sX, hj]),
      (writeW_outside _ B _ (d := 8 * kU) (by omega_using [hn, sX, hU8])).word (Or.inr (by omega_using [hU8]))
          (by omega_using [hn, sX, hj])]
  have hft : Frm B (witRanges w) s₁.mem t.mem := by
    rw [hm]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kU) (by omega_using [hn, sX, hU8])) (by simp [witRanges])).trans
      (Frm.of_outside ((writeW_outside _ B _ (d := slot w aX) (by omega_using [hn, sX])).mono (o' := slot w aX) (n' := 8 * (w + 2))
        (Nat.le_refl _) (by omega_using [])) (by simp [witRanges]))).trans
      (Frm.of_outside ((writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_using [hn, sX])).mono (o' := slot w aX)
        (n' := 8 * (w + 2)) (by omega_using []) (by omega_using [])) (by simp [witRanges]))
  have k1t := (k₂.trans k₃).trans k
  refine ⟨hc₁.of_wit hft k1t (by decide), ?_, ?_, ?_, hf₁'.trans hft, (k₁.trans k1t).mono (by decide)⟩
  · rw [hwit, ← hx₁]
    cases uu
    · exact wv_force (by omega_using [hw4]) (by rw [hw0]; rfl) (by rw [hwt]; rfl) hwm
    · exact wv_congr2 fun i hi => by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [Nat.mul_zero, Nat.add_zero, hw0]; rfl
        · by_cases hit : i = w - 1
          · rw [hit, hwt]; rfl
          · exact hwm i hi0 (by omega_using [hi, hit])
  · rw [hwit, hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_using [hn, sX])).word (d := 8 * kU)
      (Or.inl (by omega_using [hU8])) (by omega_using [hn, sX, hU8]),
      (writeW_outside _ B _ (d := slot w aX) (by omega_using [hn, sX])).word (d := 8 * kU) (Or.inl
          (by omega_using [hU8])) (by omega_using [hn, sX, hU8]),
      word_writeW_self]
  · rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_using [hn, sX])).word (d := 8 * kUsed)
      (Or.inl (by omega_using [hUs8])) (by omega_using [hn, sX, hUs8]),
      (writeW_outside _ B _ (d := slot w aX) (by omega_using [hn, sX])).word (d := 8 * kUsed) (Or.inl
          (by omega_using [hUs8])) (by omega_using [hn, sX, hUs8]),
      (writeW_outside _ B _ (d := 8 * kU) (by omega_using [hn, sX, hU8])).word (d := 8 * kUsed)
        (Or.inr (by simp only [kU, kUsed, sFn]; omega_using [])) (by omega_using [hn, sX, hUs8])]
    exact hu₁

end VG.Proof.RsaKeyGen.AArch64
