module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `RsaKeyGen.AArch64.Key.DEven`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: `d` for an even `e`

`d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`, by `inverse` modulo `L` (or
3 otherwise) (`dEven_k`, `inverse_even`).
-/

@[expose] public section

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
  obtain h₁ := h.regs m₁ k₁
  rw [WP.block_append_iff]
  refine WP.mono (evenMaskOf_k h₁ (j := aL) (by decide)) fun s₂ ⟨h₂, m₂, h15₂, _, _, k₂⟩ => ?_
  rw [m₁] at h15₂
  obtain h10₂ : s₂.gpr .x10 = mask b := (k₂.gpr .x10 (by decide)).trans h10
  obtain hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.mono (WP.keep [.x4, .x7, .x10, .x15] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
      (mask (!(decide (av I s.mem aL % 2 = 0) || b))) ∧ t.gpr .x15 = mask (decide (av I s.mem aL % 2 = 0) || b)) (by
    brun [notMask, h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15₂, h10₂, dEven_mask_or,
      dEven_mask_not]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h15t⟩, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) hm k₃
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
theorem dEven_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hee : e % 2 = 0) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (_hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dEven) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hZ := h.hZ
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  rw [dEven_eq]
  -- `[aE] := e`, `[aM] := L`, or 1 for `L = 0`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  obtain vE₁ : av I s₁.mem aE = e := av_of_full e₁ (lt_pow_W h he64)
  obtain vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₁ (j := aL) (by decide) (by decide)
    (by decide)) fun s₂ ⟨h₂, f₂, vM₂⟩ => ?_)
  rw [vL₁] at vM₂
  generalize hM₁ : dv L = M₁ at vM₂
  obtain hM₁0 : 0 < M₁ := by rw [← hM₁]; unfold dv; split <;> omega_arith
  obtain hM₁L : L ≠ 0 → M₁ = L := fun h0 => by rw [← hM₁]; unfold dv; rw [ite_eq_right_iff.mpr (fun h' => absurd h' h0)]
  obtain hok2 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  obtain vE₂ : av I s₂.mem aE = e := by rw [f₂.av hok2 (by decide) (by decide) hZ, vE₁]
  obtain vL₂ : av I s₂.mem aL = L := by rw [f₂.av hok2 (by decide) (by decide) hZ, vL₁]
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
  obtain vM₄ : av I s₄.mem aM = M₁ := by
    rw [f₄.av (by decide) (by decide) (by decide) hZ, f₃.av (by decide) (by decide) (by decide) hZ, vM₂]
  obtain vQ₄ : av I s₄.mem aQt = e := by rw [v₄, f₃.av (by decide) (by decide) (by decide) hZ, vE₂]
  rw [vM₄, vQ₄] at d₅
  obtain vR₅ : av I s₅.mem aR = e % M₁ := divmod_rem (lt_pow_W h he64) (d₅ hM₁0).1
  obtain hok5 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  obtain vU₇ : av I s₇.mem aU = e % M₁ := by rw [v₇, f₆.av (by decide) (by decide) (by decide) hZ, vR₅]
  obtain tU₇ : atop I s₇.mem aU = 0 := by rw [t₇]; exact (wv_zero2 z₆).2
  obtain vL₇ : av I s₇.mem aL = L := by
    rw [f₇.av (by decide) (by decide) (by decide) hZ, f₆.av (by decide) (by decide) (by decide) hZ,
      f₅.av hok5 (by decide) (by decide) hZ, f₄.av (by decide) (by decide) (by decide) hZ,
      f₃.av (by decide) (by decide) (by decide) hZ, vL₂]
  -- `x15 := ` the mask of `L < 3`.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA, cmpA]) (WP.mono (constA_k h₇ (x := 3) (by decide))
    fun s₈ ⟨h₈, f₈, c₈, _⟩ => ?_)
  obtain c3 : av I s₈.mem aC = 3 := av_of_full c₈ (lt_pow_W h (by decide))
  obtain vL₈ : av I s₈.mem aL = L := by rw [f₈.av (by decide) (by decide) (by decide) hZ, vL₇]
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
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  obtain f₁₀' : KF I.B I.W [.hdr kOk] s₈.mem s₁₀.mem := by rw [← m₉]; exact f₁₀
  obtain vL₁₀ : av I s₁₀.mem aL = L := by rw [f₁₀'.av hokO (by decide) (by decide) hZ, vL₈]
  obtain vC₁₂ : av I s₁₂.mem aC = 3 := by
    rw [f₁₂.av (by decide) (by decide) (by decide) hZ, f₁₁.av (by decide) (by decide) (by decide) hZ,
      f₁₀'.av hokO (by decide) (by decide) hZ, c3]
  rw [f₁₁.av (by decide) (by decide) (by decide) hZ, vL₁₀] at v₁₂
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₁₂ (j := aM) (by decide) (by decide)
    (c := bad) (by rw [k₁₂.gpr .x15 (by decide), k₁₁.gpr .x15 (by decide), h15₁₀])) fun s₁₃ ⟨h₁₃, f₁₃, v₁₃, _, _⟩ => ?_)
  rw [v₁₂, vC₁₂] at v₁₃
  generalize hM : (if bad = true then 3 else L) = M at v₁₃
  obtain hgood : bad = false → L % 2 = 1 ∧ 3 ≤ L := fun hb => by
    rw [← hbad] at hb
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    omega_using [hb]
  obtain hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]; cases hb : bad
    · have := hgood hb; simp only [Bool.false_eq_true, ite_false]; omega_using [this]
    · simp
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₁₃ (j := aM) (by decide) (by decide))
    fun s₁₄ ⟨h₁₄, f₁₄, vV₁₄, vX₁₁₄, vX₂₁₄⟩ => ?_)
  obtain hok14 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  obtain hokM : [Rc.arr aM].all Rc.ok = true := by decide
  obtain vM₁₄ : av I s₁₄.mem aM = M := by rw [f₁₄.av hok14 (by decide) (by decide) hZ, v₁₃]
  obtain presU : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
      av I m' aU = av I m aU ∧ atop I m' aU = atop I m aU := fun f ok hn =>
    ⟨f.av ok (by decide) hn hZ, f.at ok (by decide) hn hZ⟩
  obtain pU : av I s₁₄.mem aU = e % M₁ ∧ atop I s₁₄.mem aU = 0 := by
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
  obtain hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  obtain ok₁₅ : word s₁₅.mem I.B (8 * kOk) = mask (!bad) := by
    rw [f₁₅.word hokI (by decide) (by decide), f₁₄.word hok14 (by decide) (by decide),
      f₁₃.word hokM (by decide) (by decide), f₁₂.word hokM (by decide) (by decide),
      f₁₁.word hokM (by decide) (by decide), ok₁₀]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₁₅ ok₁₅)
    fun s₁₆ ⟨h₁₆, f₁₆, ok₁₆⟩ => ?_)
  rw [hg₁₅] at ok₁₆
  -- `[aDd] := x`.
  refine WP.mono (zc_k h₁₆ (o := aDd) (a := aX₂) (by decide) (by decide) (by decide)) fun t ⟨ht, f₁₇, vD, _⟩ => ?_
  obtain okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (e % M₁) M = 1) && !bad) := by
    rw [f₁₇.word (by decide) (by decide) (by decide), ok₁₆]
  obtain vDt : av I t.mem aDd = x := by
    rw [vD, f₁₆.av (by decide) (by decide) (by decide) hZ, hx]
  obtain hMe : bad = false → M = L := fun hb => by rw [← hM, hb]; rfl
  obtain hM₁e : bad = false → M₁ = L := fun hb => hM₁L (by have := hgood hb; omega_using [this])
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · exact (((((((((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans
      f₁₀').trans f₁₁).trans f₁₂).trans f₁₃).trans f₁₄).trans f₁₅).trans f₁₆).trans f₁₇).mono (by decide)
  · -- The inverse exists iff `L` is odd, at least 3, and the gcd is 1.
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1) := fun ⟨h1, h2, h3⟩ => by
        obtain hb : bad = false := by
          rw [← hbad]; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega_using [h1, h2]
        exact hc (by rw [hb, hMe hb, hM₁e hb]; simp [h3])
      rw [VG.Proof.RsaKeyGen.inverse_even_none hee this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      obtain hL3 := hgood hc.2
      have hg1 := hc.1
      rw [hMe hc.2, hM₁e hc.2] at hg1
      rw [hg₁₅, hMe hc.2, hM₁e hc.2, hg1] at hdv₁₅
      rw [hMe hc.2] at hx₁₅
      exact ⟨x, VG.Proof.RsaKeyGen.inverse_even hL3.2 (by exact_mod_cast hdv₁₅) hx₁₅⟩
  · intro d hd
    by_cases hc : L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1
    · have hb : bad = false := by
        rw [← hbad]; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega_using [hc]
      rw [hg₁₅, hMe hb, hM₁e hb, hc.2.2] at hdv₁₅
      rw [hMe hb] at hx₁₅
      rw [VG.Proof.RsaKeyGen.inverse_even hc.2.1 (by exact_mod_cast hdv₁₅) hx₁₅] at hd
      cases hd
      exact vDt
    · rw [VG.Proof.RsaKeyGen.inverse_even_none hee hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.DOdd`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: `d` for an odd `e`

`L = e Q + R`, `x = R⁻¹ mod e`, `t = e − x` (in `x1`) and `d = Q t + c` with
`c = (1 + R t) e⁻¹ mod 2⁶⁴` (in `x10`) (`dOdd_k`, `inverse_odd`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- A number below `2⁶⁴` is its low word. -/
theorem word0_of_lt {I : KIn} {m : Mem} {j v : Nat} (hw : 1 ≤ I.W) (h : av I m j = v) (hv : v < 2 ^ 64) :
    word m I.B (slot I.W j) = BitVec.ofNat 64 v :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, ← wv_mod64 _ _ _ hw,
      show wv m I.B (slot I.W j) I.W = av I m j from rfl, h, Nat.mod_eq_of_lt hv])

/-- The words of `c`: `x1 = e − x`, `x10 = ((R (e − x) + 1) e⁻¹) mod 2⁶⁴`. -/
theorem dOddC_ok {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e x R : Nat} (he64 : e < 2 ^ 64) (hxe : x < e)
    (hR : R < 2 ^ 64) (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e)
    (hX : word s.mem I.B (slot I.W aX₂) = BitVec.ofNat 64 x) (hRw : word s.mem I.B (slot I.W aR) = BitVec.ofNat 64 R) :
    WP isa (.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
      ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
        .mul .x .x10 .x3 .x4] : List Instr))) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 (e - x) ∧ ∃ einv : Nat, e * einv % 2 ^ 64 = 1 ∧
        (t.gpr .x10).toNat = ((R * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧ t.mem = s.mem) ∧
      Keep [.x1, .x3, .x4, .x5, .x6, .x10, .x11, .x12, .x15, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  obtain sX := h.ws.sl (j := aX₂) (by decide)
  obtain sR := h.ws.sl (j := aR) (by decide)
  obtain hlE := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this])
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 e ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hlE, hev]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h3₁, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (minvX4_ok s₁ (by rw [h3₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]; exact heo))
    fun s₂ ⟨⟨hinv, _, m₂⟩, k₂⟩ => ?_
  rw [h3₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64] at hinv
  generalize hei : (s₂.gpr .x4).toNat = einv at hinv
  obtain k12 := k₁.trans k₂
  obtain hs₂ := h.ws.scr.congr k12.wr
  obtain hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  rw [WP.block_append_iff]
  obtain h₂ : KS I s₀ s₂ := h.regs hm₂ k12
  refine WP.mono h₂.ws.ws_ok fun s₃ ⟨⟨_, h11, m₃, _⟩, k₃⟩ => ?_
  obtain hx0₃ : s₃.gpr .x0 = I.B := ((k12.trans k₃).gpr .x0 (by decide)).trans h.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aX₂ .x16 hx0₃ h11) fun s₄ ⟨⟨h16, m₄, _⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aR .x17 ((k₄.gpr .x0 (by decide)).trans hx0₃) ((k₄.gpr .x11 (by decide)).trans h11))
    fun s₅ ⟨⟨h17, m₅, _⟩, k₅⟩ => ?_
  obtain k25 := (k₃.trans k₄).trans k₅
  obtain hs₅ := h.ws.scr.congr ((k12.trans k25).wr)
  obtain hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, hm₂]
  obtain h16₅ : s₅.gpr .x16 = off I.B (slot I.W aX₂) := (k₅.gpr .x16 (by decide)).trans h16
  obtain hx0₅ : s₅.gpr .x0 = I.B := ((k₄.trans k₅).gpr .x0 (by decide)).trans hx0₃
  obtain h4₅ : (s₅.gpr .x4).toNat = einv := by rw [k25.gpr .x4 (by decide), hei]
  obtain hX₅ : s₅.mem.readW (off I.B (slot I.W aX₂)) 64 = BitVec.ofNat 64 x := by rw [hm₅]; exact hX
  obtain hR₅ : s₅.mem.readW (off I.B (slot I.W aR)) 64 = BitVec.ofNat 64 R := by rw [hm₅]; exact hRw
  obtain hE₅ : s₅.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₅]; exact hev
  refine WP.mono (WP.keep [.x1, .x3, .x10] (Q := fun t => t.gpr .x1 = BitVec.ofNat 64 (e - x) ∧
      (t.gpr .x10).toNat = ((R * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧ t.mem = s₅.mem) (by
    brun [hx0₅, hdr_enc (show kEv < 32 by decide), h16₅, h17,
        hs₅.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
      hs₅.ld (d := slot I.W aX₂) (by omega_using [sX]), hs₅.ld (d := slot I.W aR) (by omega_using [sR]), hX₅, hR₅, hE₅,
      VG.Offset.ofNat_sub_ofNat (Nat.le_of_lt hxe)]
    rw [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_mul, h4₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt (show e - x < 2 ^ 64 by omega_using [he64])]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h1, h10, mt⟩, kt⟩ => ?_
  exact ⟨⟨h1, einv, hinv, h10, mt.trans hm₅⟩, ((k12.trans k25).trans kt).mono (by decide)⟩

/-- `c` into `[aDd]`'s low word, and the bases for `mulAddRow`. -/
theorem dOddD_ok {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ base aDd .x8 ++ ([st .x10 .x8] : List Instr) ++ base aQt .x9 ++
      ([movi .x7 0] : List Instr))) s fun t =>
      (t.mem = s.mem.writeW (off I.B (slot I.W aDd)) (s.gpr .x10) ∧ t.gpr .x8 = off I.B (slot I.W aDd) ∧
        t.gpr .x9 = off I.B (slot I.W aQt) ∧ t.gpr .x12 = BitVec.ofNat 64 I.W ∧ t.gpr .x7 = 0) ∧
      Keep [.x7, .x8, .x9, .x11, .x12] s t := by
  have hn := h.ws.scr.nowrap
  obtain sD := h.ws.sl (j := aDd) (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  obtain hx0₁ : s₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aDd .x8 hx0₁ h11) fun s₂ ⟨⟨h8, m₂, _⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  obtain hs₂ := h.ws.scr.congr (k₁.trans k₂).wr
  obtain h10₂ : s₂.gpr .x10 = s.gpr .x10 := (k₁.trans k₂).gpr .x10 (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aDd)) (s.gpr .x10)) (by
    brun [h8, hs₂.st (d := slot I.W aDd) (by omega_using [sD]), h10₂, m₂, m₁]) rfl rfl rfl) fun s₃ ⟨m₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  obtain k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (base_ok aQt .x9 ((k13.gpr .x0 (by decide)).trans h.ws.x0) (((k₂.trans k₃).gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h9, m₄, _⟩, k₄⟩ => ?_
  refine WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = s₄.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨h7, m₅⟩, k₅⟩ => ?_
  obtain k35 := (k₃.trans k₄).trans k₅
  exact ⟨⟨by rw [m₅, m₄, m₃], (k35.gpr .x8 (by decide)).trans h8, (k₅.gpr .x9 (by decide)).trans h9,
    (((k₂.trans k35).gpr .x12 (by decide))).trans h12, h7⟩, (k13.trans (k₄.trans k₅)).mono (by decide)⟩

theorem dOdd_eq : dOdd = loadEv ++ (([zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] :
    List (Prog isa)) ++ (invFrom aE ++ (([inverse aU aV aX₁ aX₂ aE aT] : List (Prog isa)) ++ (lGe2 ++ (gcdIsOne ++
    ([.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
        ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
          .mul .x .x10 .x3 .x4] : List Instr)),
      zeroA aDd,
      .block (ws ++ base aDd .x8 ++ ([st .x10 .x8] : List Instr) ++ base aQt .x9 ++ ([movi .x7 0] : List Instr)),
      mulAddRow] : List (Prog isa))))))) := by
  simp only [dOdd, List.append_assoc]

/-- `dOdd`, for an odd `e ≥ 3`. -/
theorem dOdd_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he3 : 3 ≤ e) (he64 : e < 2 ^ 64)
    (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dOdd) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  have hw2 := h.ws.w2
  rw [dOdd_eq]
  -- `[aE] := e`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  obtain vE₁ : av I s₁.mem aE = e := av_of_full e₁ (lt_pow_W h he64)
  obtain vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  -- `L = e Q + R`.
  refine wp_seqs_append (by simp) (by simp [invFrom]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aQt) (by decide)) fun s₂ ⟨h₂, f₂, _, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aQt) (a := aL) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aQt) (iR := aR) (iD := aE) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aU) (by decide)) fun s₅ ⟨h₅, f₅, z₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, t₆, _⟩ => ?_))))
  obtain vE₃ : av I s₃.mem aE = e := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vE₁]
  obtain vQ₃ : av I s₃.mem aQt = L := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  rw [vE₃, vQ₃] at d₄
  obtain ⟨dR, dQ⟩ := d₄ (by omega_using [heo])
  obtain hR : L % e < e := Nat.mod_lt _ (by omega_using [heo])
  obtain vR₄ : av I s₄.mem aR = L % e := divmod_rem hLW dR
  obtain hok4 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  obtain vU₆ : av I s₆.mem aU = L % e := by rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  obtain tU₆ : atop I s₆.mem aU = 0 := by rw [t₆]; exact (wv_zero2 z₅).2
  obtain pres6 : ∀ j, j < 16 → j ≠ aQt → j ≠ aR → j ≠ aT → j ≠ aU → av I s₆.mem j = av I s₃.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ]
  obtain vE₆ : av I s₆.mem aE = e := by rw [pres6 aE (by decide) (by decide) (by decide) (by decide) (by decide), vE₃]
  obtain vQ₆ : av I s₆.mem aQt = L / e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, dQ]
  obtain vR₆ : av I s₆.mem aR = L % e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  obtain vL₆ : av I s₆.mem aL = L := by
    rw [pres6 aL (by decide) (by decide) (by decide) (by decide) (by decide), f₃.av (by decide) (by decide)
      (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  -- `x = R⁻¹ mod e`.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₆ (j := aE) (by decide) (by decide))
    fun s₇ ⟨h₇, f₇, vV₇, vX₁₇, vX₂₇⟩ => ?_)
  obtain hok7 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  obtain vU₇ : av I s₇.mem aU = L % e := by rw [f₇.av hok7 (by decide) (by decide) hZ, vU₆]
  obtain tU₇ : atop I s₇.mem aU = 0 := by rw [f₇.at hok7 (by decide) (by decide) hZ, tU₆]
  obtain vE₇ : av I s₇.mem aE = e := by rw [f₇.av hok7 (by decide) (by decide) hZ, vE₆]
  refine wp_seqs_append (by simp) (by simp [lGe2]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₇ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aE) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) tU₇ (by rw [vV₇, vE₆, vE₇]) vX₁₇ vX₂₇) fun s₈ ⟨h₈, f₈, hinv⟩ => ?_
  rw [vE₇, vU₇] at hinv
  obtain ⟨hg₈, hdv₈, hx₈⟩ := hinv heo (by omega_using [he3])
  generalize hx : av I s₈.mem aX₂ = x at hdv₈ hx₈
  obtain hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  obtain vL₈ : av I s₈.mem aL = L := by
    rw [f₈.av hokI (by decide) (by decide) hZ, f₇.av hok7 (by decide) (by decide) hZ, vL₆]
  -- `kOk := ` the masks of `L ≥ 2` and `gcd(R, e) = 1`.
  refine wp_seqs_append (by simp [lGe2, constA]) (by simp [gcdIsOne, constA]) (WP.mono (lGe2_k h₈)
    fun s₉ ⟨h₉, f₉, ok₉⟩ => ?_)
  rw [vL₈] at ok₉
  obtain vV₉ : av I s₉.mem aV = Nat.gcd (L % e) e := by rw [f₉.av (by decide) (by decide) (by decide) hZ, hg₈]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₉ ok₉)
    fun s₁₀ ⟨h₁₀, f₁₀, ok₁₀⟩ => ?_)
  rw [vV₉] at ok₁₀
  obtain hokC : [Rc.arr aC, Rc.hdr kOk].all Rc.ok = true := by decide
  obtain pres10 : ∀ j, j < 16 → j ≠ aC → av I s₁₀.mem j = av I s₈.mem j := fun j hj h1 => by
    rw [f₁₀.av hokC hj (by simp [h1]) hZ, f₉.av hokC hj (by simp [h1]) hZ]
  have hxe : x < e := hx₈
  obtain vX₁₀ : av I s₁₀.mem aX₂ = x := by rw [pres10 aX₂ (by decide) (by decide), hx]
  obtain vR₁₀ : av I s₁₀.mem aR = L % e := by
    rw [pres10 aR (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ,
      f₇.av hok7 (by decide) (by decide) hZ, vR₆]
  obtain vQ₁₀ : av I s₁₀.mem aQt = L / e := by
    rw [pres10 aQt (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ,
      f₇.av hok7 (by decide) (by decide) hZ, vQ₆]
  obtain hev₁₀ : word s₁₀.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by
    obtain hk : ∀ {cs : List Rc} {m m' : Mem}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .hdr kEv ∉ cs →
        word m' I.B (8 * kEv) = word m I.B (8 * kEv) := fun f ok hn => f.word ok (by decide) hn
    rw [hk f₁₀ hokC (by decide), hk f₉ hokC (by decide), hk f₈ hokI (by decide), hk f₇ hok7 (by decide),
      hk f₆ (by decide) (by decide), hk f₅ (by decide) (by decide), hk f₄ hok4 (by decide),
      hk f₃ (by decide) (by decide), hk f₂ (by decide) (by decide), hk f₁ (by decide) (by decide), hev]
  -- `x1 := e − x`, `x10 := c`.
  simp only [seqs]
  refine WP.seq (WP.mono (dOddC_ok h₁₀ he64 hxe (Nat.lt_trans hR he64) heo hev₁₀
    (word0_of_lt hw1 vX₁₀ (Nat.lt_trans hxe he64)) (word0_of_lt hw1 vR₁₀ (Nat.lt_trans hR he64)))
    fun s₁₁ ⟨⟨h1₁₁, einv, hinv₁₁, c₁₁, m₁₁⟩, k₁₁⟩ => ?_)
  obtain h₁₁ := h₁₀.regs m₁₁ k₁₁
  generalize hcv : ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 = c at c₁₁
  -- `[aDd] := c`.
  refine WP.seq (WP.mono (zeroA_k h₁₁ (j := aDd) (by decide)) fun s₁₂ ⟨h₁₂, f₁₂, z₁₂, _, k₁₂⟩ => ?_)
  refine WP.seq (WP.mono (dOddD_ok h₁₂) fun s₁₃ ⟨⟨m₁₃, h8, h9, h12, h7⟩, k₁₃⟩ => ?_)
  obtain sD := h.ws.sl (j := aDd) (by decide)
  obtain sQ := h.ws.sl (j := aQt) (by decide)
  obtain spDQ := slot_sep (w := I.W) (j := aDd) (k := aQt) (by decide)
  obtain o₁₃ := writeW_outside s₁₂.mem I.B (s₁₂.gpr .x10) (d := slot I.W aDd) (by omega_using [hn, sD])
  rw [← m₁₃] at o₁₃
  obtain f₁₃ := KF.arr1 (B := I.B) (W := I.W) (j := aDd) o₁₃ (Nat.le_refl _) (by omega_using [])
  obtain h₁₃ := h₁₂.step f₁₃ (all_mut_arr (by decide)) k₁₃
  obtain c₁₂ : (s₁₂.gpr .x10).toNat = c := by rw [k₁₂.gpr .x10 (by decide)]; exact c₁₁
  obtain vD₁₃ : wv s₁₃.mem I.B (slot I.W aDd) (I.W + 2) = c := by
    rw [m₁₃, wv_put0 _ z₁₂ (by omega_using [hn, sD]), c₁₂]
  obtain hokD : [Rc.arr aDd].all Rc.ok = true := by decide
  obtain vQ₁₃ : av I s₁₃.mem aQt = L / e := by
    rw [f₁₃.av hokD (by decide) (by decide) hZ, f₁₂.av hokD (by decide) (by decide) hZ,
      show av I s₁₁.mem aQt = av I s₁₀.mem aQt by rw [m₁₁], vQ₁₀]
  obtain h1₁₃ : s₁₃.gpr .x1 = BitVec.ofNat 64 (e - x) := by
    rw [k₁₃.gpr .x1 (by decide), k₁₂.gpr .x1 (by decide), h1₁₁]
  -- `[aDd] += t Q`.
  obtain hcl : c < 2 ^ 64 := by rw [← hcv]; exact Nat.mod_lt _ (by decide)
  obtain hQ : L / e < 2 ^ (64 * I.W) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLW
  obtain hbound : c + (e - x) * (L / e) < 2 ^ (64 * (I.W + 2)) := by
    obtain h1 : (e - x) * (L / e) < 2 ^ 64 * 2 ^ (64 * I.W) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega_using [he64]) (Nat.le_of_lt hQ) (by omega_using [dQ, hQ])
    obtain h2 : 2 ^ 64 + 2 ^ 64 * 2 ^ (64 * I.W) ≤ 2 ^ (64 * (I.W + 2)) := by
      rw [show 64 * (I.W + 2) = 64 + 64 + 64 * I.W by omega_using [], Nat.pow_add, Nat.pow_add]
      have : 1 ≤ 2 ^ (64 * I.W) := Nat.one_le_two_pow
      have : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * I.W) := Nat.le_mul_of_pos_right _ (by omega_using [this])
      have : 2 * (2 ^ 64 * 2 ^ (64 * I.W)) ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ (64 * I.W) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega_arith
    omega_using [hcl, h1, h2]
  have vQ' : wv s₁₃.mem I.B (slot I.W aQt) I.W = L / e := vQ₁₃
  obtain hex : (s₁₃.gpr .x1).toNat = e - x := by
    rw [h1₁₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [he64])]
  refine WP.mono (mulAddRow_ok h₁₃.ws.scr h8 h9 h12 h7 hw1 (by omega_using [hw2]) (by omega_using [sD])
      (by omega_using [sQ]) (by omega_using [spDQ])
    (by rw [vD₁₃, hex, vQ']; exact hbound)) fun t ⟨hv, o, kt⟩ => ?_
  rw [vD₁₃, hex, vQ'] at hv
  obtain ft := KF.arr1 (B := I.B) (W := I.W) (j := aDd) o (Nat.le_refl _) (Nat.le_refl _)
  obtain ht := h₁₃.step ft (all_mut_arr (by decide)) kt
  obtain okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (L % e) e = 1) && decide (2 ≤ L)) := by
    rw [ft.word hokD (by decide) (by decide), f₁₃.word hokD (by decide) (by decide),
      f₁₂.word hokD (by decide) (by decide), m₁₁, ok₁₀]
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · have f₁₁ : KF I.B I.W [] s₁₀.mem s₁₁.mem := KF.of_eq m₁₁
    exact (((((((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).trans f₁₁).trans f₁₂).trans f₁₃).trans ft).mono (by decide)
  · -- The inverse exists iff both hold.
    obtain hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (2 ≤ L ∧ Nat.gcd (L % e) e = 1) := fun ⟨h1, h2⟩ => hc (by simp [h1, h2])
      rw [VG.Proof.RsaKeyGen.inverse_odd_none he3 hQR this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.1] at this; exact_mod_cast this
      exact ⟨_, VG.Proof.RsaKeyGen.inverse_odd he3 he64 hc.2 hQR hR hx1 hxe hinv₁₁⟩
  · intro d hd
    by_cases hc : 2 ≤ L ∧ Nat.gcd (L % e) e = 1
    · have hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
      obtain hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.2] at this; exact_mod_cast this
      obtain hio := VG.Proof.RsaKeyGen.inverse_odd he3 he64 hc.1 hQR hR hx1 hxe hinv₁₁
      rw [hcv] at hio
      obtain hdL := (VG.Proof.RsaKeyGen.inverse_some hio).2 (by omega_using [hc])
      rw [hio] at hd
      cases hd
      exact av_of_full (by rw [hv, Nat.add_comm, Nat.mul_comm]) (by omega_using [hLW, hdL])
    · rw [VG.Proof.RsaKeyGen.inverse_odd_none he3 (Nat.div_add_mod L e).symm hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# An RSA key from its primes on AArch64: `d = e⁻¹ mod L`

`dPart`, by `e` (`cbz`/`cbnz` on `x3`): none for 0 (`dZero`), 1 for 1 but
`L = 1` (`dOne_k`), `dOdd` for an odd `e` and `dEven` for an even one
(`dPart_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- `e = 1`: `d = 1`, `kOk` the mask of `L ≠ 1`. -/
theorem dOne_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {L : Nat} (hL : av I s.mem aL = L) :
    WP isa (seqs dOne) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I 1 L t.mem := by
  have hZ := h.hZ
  unfold dOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [neMask, eqA]) (WP.mono (constA_k h (x := 1) (by decide))
    fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  obtain c1 : av I s₁.mem aC = 1 := av_of_full c₁ (lt_pow_W h (by decide))
  obtain vL : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp [neMask, eqA]) (by simp) (WP.mono (neMask_k h₁ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, h15, _, _⟩ => ?_)
  rw [vL, c1] at h15
  simp only [seqs]
  obtain hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.seq (WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (L = 1)))) (by brun [h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15]) rfl rfl rfl)
    fun s₃ ⟨m₃, k₃⟩ => ?_)
  obtain ⟨h₃, f₃, ok₃⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) m₃ k₃
  refine WP.seq (WP.mono (zeroA_k h₃ (j := aDd) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _, _⟩ =>
    WP.mono (setOne_k h₄ (j := aDd) (by decide) z₄) fun t ⟨ht, f₅, o₅, _⟩ => ?_)
  refine ⟨ht, (((f₁.trans (by rw [← m₂]; exact f₃)).trans f₄).trans f₅).mono (by decide),
    ⟨!decide (L = 1), ?_, ?_, ?_⟩⟩
  · rw [f₅.word (by decide) (by decide) (by decide), f₄.word (by decide) (by decide) (by decide), ok₃]
  · rw [VG.Proof.RsaKeyGen.inverse_one]
    by_cases h1 : L = 1 <;> simp [h1]
  · intro d hd
    rw [VG.Proof.RsaKeyGen.inverse_one] at hd
    by_cases h1 : L = 1
    · simp [h1] at hd
    · simp only [h1, ite_false, Option.some.injEq] at hd
      subst hd
      exact av_of_full o₅ (lt_pow_W h (by decide))

/-- A word's test against zero. -/
theorem ofNat_beq_zero {e : Nat} (he : e < 2 ^ 64) : (BitVec.ofNat 64 e == 0) = decide (e = 0) := by
  by_cases h : e = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 e ≠ 0 := fun h' => h (by
      have := congrArg BitVec.toNat h'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he] at this)
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- `dPart`, for `e < 2⁶⁴`. -/
theorem dPart_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L) (hLW : L < 2 ^ (64 * I.W)) :
    WP isa dPart s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  obtain hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this])
  unfold dPart
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 e ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hld, hev]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h3₁, m₁⟩, k₁⟩ => ?_)
  obtain h₁ := h.regs m₁ k₁
  obtain hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₁, hev]
  obtain hL₁ : av I s₁.mem aL = L := by rw [show av I s₁.mem aL = av I s.mem aL by rw [m₁], hL]
  obtain post : ∀ {u : State}, u.mem = s.mem → ∀ t, KS I s₀ t ∧ KF I.B I.W csD u.mem t.mem ∧ DRes I e L t.mem →
      KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := fun hu t ⟨a, b, c⟩ =>
    ⟨a, by rw [← hu]; exact b, c⟩
  refine WP.ite (decide (e = 0)) (by rw [VG.Proof.MlKem.AArch64.eval_zero, h3₁, ofNat_beq_zero he64])
    (fun he0 => ?_) (fun he0 => ?_)
  · -- `e = 0`: no inverse.
    simp only [decide_eq_true_eq] at he0
    obtain hst := h₁.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (8 * kOk)) (mask false)) (by
      unfold dZero
      brun [h₁.ws.x0, hdr_enc (show kOk < 32 by decide), hst]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨m, k⟩ => post m₁ t ?_
    obtain ⟨ht, ft, okt⟩ := h₁.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) m k
    refine ⟨ht, ft.mono (by decide), false, okt, ?_, fun d hd => ?_⟩
    · rw [he0, VG.Proof.RsaKeyGen.inverse_zero]; simp
    · rw [he0, VG.Proof.RsaKeyGen.inverse_zero] at hd; cases hd
  simp only [decide_eq_false_iff_not] at he0
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (e - 1) ∧ t.mem = s₁.mem) (by
    brun [h3₁]
    exact VG.Offset.ofNat_sub_ofNat (by omega_using [he0])) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h3₂, m₂⟩, k₂⟩ => ?_)
  obtain h₂ := h₁.regs m₂ k₂
  obtain hm₂ : s₂.mem = s.mem := m₂.trans m₁
  refine WP.ite (decide (e = 1)) (by
      rw [VG.Proof.MlKem.AArch64.eval_zero, h3₂, ofNat_beq_zero (by omega_using [he64])]
      congr 1; exact decide_eq_decide.mpr (by omega_using [he0]))
    (fun he1 => ?_) (fun he1 => ?_)
  · simp only [decide_eq_true_eq] at he1
    subst he1
    exact WP.mono (dOne_k h₂ (by rw [show av I s₂.mem aL = av I s₁.mem aL by rw [m₂], hL₁])) (post hm₂)
  simp only [decide_eq_false_iff_not] at he1
  obtain hev₂ : word s₂.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₂, hev₁]
  obtain hld₂ := h₂.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this])
  refine WP.seq (WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (e % 2) ∧ t.mem = s₂.mem) (by
    brun [h₂.ws.x0, hdr_enc (show kEv < 32 by decide), hld₂, hev₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega_using []) (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h3₃, m₃⟩, k₃⟩ => ?_)
  obtain h₃ := h₂.regs m₃ k₃
  obtain hm₃ : s₃.mem = s.mem := m₃.trans hm₂
  obtain hev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [hm₃, hev]
  obtain hL₃ : av I s₃.mem aL = L := by rw [show av I s₃.mem aL = av I s.mem aL by rw [hm₃], hL]
  refine WP.ite (decide (e % 2 = 1)) (by
      rw [VG.Proof.MlKem.AArch64.eval_nonzero, h3₃]
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2 <;> rw [h2] <;> decide)
    (fun ho => ?_) (fun ho => ?_)
  · simp only [decide_eq_true_eq] at ho
    exact WP.mono (dOdd_k h₃ (by omega_using [he1, ho]) he64 ho hev₃ hL₃ hLW) (post hm₃)
  · simp only [decide_eq_false_iff_not] at ho
    exact WP.mono (dEven_k h₃ he64 (by omega_using [ho]) hev₃ hL₃ hLW) (post hm₃)

end VG.Proof.RsaKeyGen.AArch64.Key
