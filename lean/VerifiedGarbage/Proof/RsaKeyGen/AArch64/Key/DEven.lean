import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath

/-!
# An RSA key from its primes on AArch64: `d` for an even `e`

`d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`, by `inverse` modulo `L` (or
3 otherwise) (`dEven_k`, `inverse_even`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem dEven_mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

/-- `notMask`'s value. -/
theorem dEven_mask_not (c : Bool) : mask c ^^^ BitVec.setWidth 64 0#16 - 1#64 = mask (!c) := by cases c <;> decide

/-- The mask of `L` even or below 3 (`b`, the mask of `L < 3`, in `x15`)
into `x15`, its complement into `kOk`. -/
theorem dEvenMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {b : Bool} (h15 : s.gpr .x15 = mask b) :
    WP isa (.block (([mov .x10 .x15] : List Instr) ++ evenMaskOf aL ++
      ([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ notMask ++
      ([sth .x15 kOk, mov .x15 .x10] : List Instr))) s fun t =>
      KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
        word t.mem I.B (8 * kOk) = mask (!(decide (av I s.mem aL % 2 = 0) || b)) ∧
        t.gpr .x15 = mask (decide (av I s.mem aL % 2 = 0) || b) := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 = mask b ∧ t.mem = s.mem) (by brun [h15])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h10, m₁⟩, k₁⟩ => ?_
  have h₁ := h.regs m₁ k₁
  rw [WP.block_append_iff]
  refine WP.mono (evenMaskOf_k h₁ (j := aL) (by decide)) fun s₂ ⟨h₂, m₂, h15₂, _, _, k₂⟩ => ?_
  rw [m₁] at h15₂
  have h10₂ : s₂.gpr .x10 = mask b := (k₂.gpr .x10 (by decide)).trans h10
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.x4, .x7, .x10, .x15] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
      (mask (!(decide (av I s.mem aL % 2 = 0) || b))) ∧ t.gpr .x15 = mask (decide (av I s.mem aL % 2 = 0) || b)) (by
    brun [notMask, h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15₂, h10₂, dEven_mask_or,
      dEven_mask_not]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h15t⟩, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃
  exact ⟨ht, by rw [m₁, ← m₂] at *; exact f₃, hw, h15t⟩

theorem dEven_eq : dEven = loadEv ++ (divisorOf aL ++
    (([zeroA aQt, copyA aQt aE, divmod aQt aR aM aT, zeroA aU, copyA aU aR] : List (Prog isa)) ++ (constA 3 ++
    (ltA aL aC ++ (([.block (([mov .x10 .x15] : List Instr) ++ evenMaskOf aL ++
        ([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ notMask ++
        ([sth .x15 kOk, mov .x15 .x10] : List Instr)),
      zeroA aM, copyA aM aL] : List (Prog isa)) ++ (selC aM ++ (invFrom aM ++
    (([inverse aU aV aX₁ aX₂ aM aT] : List (Prog isa)) ++ (gcdIsOne ++
    ([zeroA aDd, copyA aDd aX₂] : List (Prog isa))))))))))) := by
  simp only [dEven, List.append_assoc]

/-- `dEven`, for an even `e` (any `L`: `divmod` divides `e`, a word, by `L` or 1). -/
theorem dEven_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hee : e % 2 = 0) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (_hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dEven) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  rw [dEven_eq]
  -- `[aE] := e`, `[aM] := L`, or 1 for `L = 0`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  have vE₁ : av I s₁.mem aE = e := av_of_full e₁ (lt_pow_W h he64)
  have vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₁ (j := aL) (by decide) (by decide)
    (by decide)) fun s₂ ⟨h₂, f₂, vM₂⟩ => ?_)
  rw [vL₁] at vM₂
  generalize hM₁ : dv L = M₁ at vM₂
  have hM₁0 : 0 < M₁ := by rw [← hM₁]; unfold dv; split <;> omega
  have hM₁L : L ≠ 0 → M₁ = L := fun h0 => by rw [← hM₁]; unfold dv; rw [ite_eq_right_iff.mpr (fun h' => absurd h' h0)]
  have hok2 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  have vE₂ : av I s₂.mem aE = e := by rw [f₂.av hok2 (by decide) (by decide) hZ, vE₁]
  have vL₂ : av I s₂.mem aL = L := by rw [f₂.av hok2 (by decide) (by decide) hZ, vL₁]
  -- `[aR] := e mod M₁`, `[aU] := [aR]`.
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₂ (j := aQt) (by decide)) fun s₃ ⟨h₃, f₃, _, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₃ (o := aQt) (a := aE) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, v₄, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₄ (iQ := aQt) (iR := aR) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨h₅, f₅, d₅⟩ =>
        WP.seq (WP.mono (zeroA_k h₅ (j := aU) (by decide)) fun s₆ ⟨h₆, f₆, z₆, _, _⟩ =>
          WP.mono (copyA_k h₆ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₇ ⟨h₇, f₇, v₇, t₇, _⟩ => ?_))))
  have vM₄ : av I s₄.mem aM = M₁ := by
    rw [f₄.av (by decide) (by decide) (by decide) hZ, f₃.av (by decide) (by decide) (by decide) hZ, vM₂]
  have vQ₄ : av I s₄.mem aQt = e := by rw [v₄, f₃.av (by decide) (by decide) (by decide) hZ, vE₂]
  rw [vM₄, vQ₄] at d₅
  have vR₅ : av I s₅.mem aR = e % M₁ := divmod_rem (lt_pow_W h he64) (d₅ hM₁0).1
  have hok5 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  have vU₇ : av I s₇.mem aU = e % M₁ := by rw [v₇, f₆.av (by decide) (by decide) (by decide) hZ, vR₅]
  have tU₇ : atop I s₇.mem aU = 0 := by rw [t₇]; exact (wv_zero2 z₆).2
  have vL₇ : av I s₇.mem aL = L := by
    rw [f₇.av (by decide) (by decide) (by decide) hZ, f₆.av (by decide) (by decide) (by decide) hZ,
      f₅.av hok5 (by decide) (by decide) hZ, f₄.av (by decide) (by decide) (by decide) hZ,
      f₃.av (by decide) (by decide) (by decide) hZ, vL₂]
  -- `x15 := ` the mask of `L < 3`.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA, cmpA]) (WP.mono (constA_k h₇ (x := 3) (by decide))
    fun s₈ ⟨h₈, f₈, c₈, _⟩ => ?_)
  have c3 : av I s₈.mem aC = 3 := av_of_full c₈ (lt_pow_W h (by decide))
  have vL₈ : av I s₈.mem aL = L := by rw [f₈.av (by decide) (by decide) (by decide) hZ, vL₇]
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₈ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₉ ⟨h₉, m₉, h15₉, _, _⟩ => ?_)
  rw [vL₈, c3] at h15₉
  -- `kOk := ` the mask of `L` odd and at least 3, `x15` its complement.
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (dEvenMask_k h₉ h15₉) fun s₁₀ ⟨h₁₀, f₁₀, ok₁₀, h15₁₀⟩ => ?_)
  rw [m₉, vL₈] at ok₁₀ h15₁₀
  generalize hbad : (decide (L % 2 = 0) || decide (L < 3)) = bad at ok₁₀ h15₁₀
  -- `[aM] := L`, then 3 if `bad`.
  refine WP.seq (WP.mono (zeroA_k h₁₀ (j := aM) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, _, _, k₁₁⟩ =>
    WP.mono (copyA_k h₁₁ (o := aM) (a := aL) (by decide) (by decide) (by decide)) fun s₁₂ ⟨h₁₂, f₁₂, v₁₂, _, k₁₂⟩ => ?_)
  have hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  have f₁₀' : KF I.B I.W [.hdr kOk] s₈.mem s₁₀.mem := by rw [← m₉]; exact f₁₀
  have vL₁₀ : av I s₁₀.mem aL = L := by rw [f₁₀'.av hokO (by decide) (by decide) hZ, vL₈]
  have vC₁₂ : av I s₁₂.mem aC = 3 := by
    rw [f₁₂.av (by decide) (by decide) (by decide) hZ, f₁₁.av (by decide) (by decide) (by decide) hZ,
      f₁₀'.av hokO (by decide) (by decide) hZ, c3]
  rw [f₁₁.av (by decide) (by decide) (by decide) hZ, vL₁₀] at v₁₂
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₁₂ (j := aM) (by decide) (by decide)
    (c := bad) (by rw [k₁₂.gpr .x15 (by decide), k₁₁.gpr .x15 (by decide), h15₁₀])) fun s₁₃ ⟨h₁₃, f₁₃, v₁₃, _, _⟩ => ?_)
  rw [v₁₂, vC₁₂] at v₁₃
  generalize hM : (if bad = true then 3 else L) = M at v₁₃
  have hgood : bad = false → L % 2 = 1 ∧ 3 ≤ L := fun hb => by
    rw [← hbad] at hb
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    omega
  have hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]; cases hb : bad
    · have := hgood hb; simp only [Bool.false_eq_true, ite_false]; omega
    · simp
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₁₃ (j := aM) (by decide) (by decide))
    fun s₁₄ ⟨h₁₄, f₁₄, vV₁₄, vX₁₁₄, vX₂₁₄⟩ => ?_)
  have hok14 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  have hokM : [Rc.arr aM].all Rc.ok = true := by decide
  have vM₁₄ : av I s₁₄.mem aM = M := by rw [f₁₄.av hok14 (by decide) (by decide) hZ, v₁₃]
  have presU : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
      av I m' aU = av I m aU ∧ atop I m' aU = atop I m aU := fun f ok hn =>
    ⟨f.av ok (by decide) hn hZ, f.at ok (by decide) hn hZ⟩
  have pU : av I s₁₄.mem aU = e % M₁ ∧ atop I s₁₄.mem aU = 0 := by
    obtain ⟨a1, b1⟩ := presU f₁₄ hok14 (by decide)
    obtain ⟨a2, b2⟩ := presU f₁₃ hokM (by decide)
    obtain ⟨a3, b3⟩ := presU f₁₂ hokM (by decide)
    obtain ⟨a4, b4⟩ := presU f₁₁ hokM (by decide)
    obtain ⟨a5, b5⟩ := presU f₁₀' hokO (by decide)
    obtain ⟨a6, b6⟩ := presU f₈ (by decide) (by decide)
    exact ⟨by rw [a1, a2, a3, a4, a5, a6, vU₇], by rw [b1, b2, b3, b4, b5, b6, tU₇]⟩
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₁₄ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pU.2 (by rw [vV₁₄, v₁₃, vM₁₄]) vX₁₁₄ vX₂₁₄) fun s₁₅ ⟨h₁₅, f₁₅, hinv⟩ => ?_
  rw [vM₁₄, pU.1] at hinv
  obtain ⟨hg₁₅, hdv₁₅, hx₁₅⟩ := hinv hMo.1 hMo.2
  generalize hx : av I s₁₅.mem aX₂ = x at hdv₁₅ hx₁₅
  -- `kOk &= ` the mask of the gcd being 1.
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  have ok₁₅ : word s₁₅.mem I.B (8 * kOk) = mask (!bad) := by
    rw [f₁₅.word hokI (by decide) (by decide), f₁₄.word hok14 (by decide) (by decide),
      f₁₃.word hokM (by decide) (by decide), f₁₂.word hokM (by decide) (by decide),
      f₁₁.word hokM (by decide) (by decide), ok₁₀]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₁₅ ok₁₅)
    fun s₁₆ ⟨h₁₆, f₁₆, ok₁₆⟩ => ?_)
  rw [hg₁₅] at ok₁₆
  -- `[aDd] := x`.
  refine WP.mono (zc_k h₁₆ (o := aDd) (a := aX₂) (by decide) (by decide) (by decide)) fun t ⟨ht, f₁₇, vD, _⟩ => ?_
  have okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (e % M₁) M = 1) && !bad) := by
    rw [f₁₇.word (by decide) (by decide) (by decide), ok₁₆]
  have vDt : av I t.mem aDd = x := by
    rw [vD, f₁₆.av (by decide) (by decide) (by decide) hZ, hx]
  have hMe : bad = false → M = L := fun hb => by rw [← hM, hb]; rfl
  have hM₁e : bad = false → M₁ = L := fun hb => hM₁L (by have := hgood hb; omega)
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · exact (((((((((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans
      f₁₀').trans f₁₁).trans f₁₂).trans f₁₃).trans f₁₄).trans f₁₅).trans f₁₆).trans f₁₇).mono (by decide)
  · -- The inverse exists iff `L` is odd, at least 3, and the gcd is 1.
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1) := fun ⟨h1, h2, h3⟩ => by
        have hb : bad = false := by
          rw [← hbad]; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
        exact hc (by rw [hb, hMe hb, hM₁e hb]; simp [h3])
      rw [VG.Proof.RsaKeyGen.inverse_even_none hee this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      have hL3 := hgood hc.2
      have hg1 := hc.1
      rw [hMe hc.2, hM₁e hc.2] at hg1
      rw [hg₁₅, hMe hc.2, hM₁e hc.2, hg1] at hdv₁₅
      rw [hMe hc.2] at hx₁₅
      exact ⟨x, VG.Proof.RsaKeyGen.inverse_even hL3.2 (by exact_mod_cast hdv₁₅) hx₁₅⟩
  · intro d hd
    by_cases hc : L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1
    · have hb : bad = false := by
        rw [← hbad]; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
      rw [hg₁₅, hMe hb, hM₁e hb, hc.2.2] at hdv₁₅
      rw [hMe hb] at hx₁₅
      rw [VG.Proof.RsaKeyGen.inverse_even hc.2.1 (by exact_mod_cast hdv₁₅) hx₁₅] at hd
      cases hd
      exact vDt
    · rw [VG.Proof.RsaKeyGen.inverse_even_none hee hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.AArch64.Key
