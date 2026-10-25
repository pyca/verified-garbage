module
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.Ranges

/-!
# An FFDH parameter candidate on AArch64: Montgomery arithmetic modulo `N`

`montPrep` (`montPrep_ok`): RSA's `montSetup` without its count of checks,
for any odd `N` of `w` words whose top word is not zero and `w ≤ 128`:
`-N⁻¹`, the number 1, `R² mod N`, `R mod N` and `N − R mod N`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- What `montPrep` changes after `-N⁻¹`. -/
def mpTail (w : Nat) : List (Nat × Nat) :=
  [(slot w aOne, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aR2, 8 * (w + 2)), (8 * sCnt, 8), (slot w aY, 8 * (w + 2)), (slot w aR1, 8 * (w + 2)),
    (slot w aRm1, 8 * (w + 2))]

/-- What `montPrep` changes. -/
def mpRanges (w : Nat) : List (Nat × Nat) := (8 * sMinv, 8) :: mpTail w

theorem mpRanges_kmut (w : Nat) : ∀ r ∈ mpRanges w, KMut r := by
  simp only [mpRanges, mpTail, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first | exact KMut.ofSlot w _ _ | exact KMut.hdr (by decide)

theorem mpTail_kmut (w : Nat) : ∀ r ∈ mpTail w, KMut r :=
  fun r hr => mpRanges_kmut w r (List.mem_cons_of_mem _ hr)

theorem mpRanges_pmut (w : Nat) : ∀ r ∈ mpRanges w, PMut r := by
  simp only [mpRanges, mpTail, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first | exact PMut.ofSlot w _ _ | exact PMut.hdr (by decide)

theorem mpRanges_le {w Z : Nat} (hZ : slot w 16 ≤ Z) : ∀ r ∈ mpRanges w, r.1 + r.2 ≤ Z := by
  simp only [mpRanges, mpTail, List.mem_cons, List.not_mem_nil, or_false]
  simp only [slot, hdrBytes] at hZ
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [slot, hdrBytes, aOne, aAcc, aTmp, aR2, aY, aR1, aRm1, sCnt, sFn, sMinv] <;> omega_arith

/-- Disjointness of a range from `mpTail`'s. -/
tactic_template "mp_disj" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, mpTail, r2Ranges, slot,
    hdrBytes, aN, aAcc, aTmp, aR2, aY, aOne, aR1, aRm1, sCnt, sFn, sMinv]
  and_intros <;> omega_arith))

/-- `mpTail` keeps `-N⁻¹` and `N`. -/
theorem mp_fix {B : Addr} {Z w : Nat} {m m' : Mem} (f : Frm B (mpTail w) m m') (hz : B.toNat + Z ≤ 2 ^ 64)
    (hZ : slot w 16 ≤ Z) :
    word m' B (8 * sMinv) = word m B (8 * sMinv) ∧ word m' B (slot w aN) = word m B (slot w aN) ∧
      wv m' B (slot w aN) w = wv m B (slot w aN) w := by
  simp only [slot, hdrBytes] at hZ
  refine ⟨f.word_eq (by mp_disj) (by simp only [sMinv]; omega_arith),
    f.word_eq (by mp_disj) (by simp only [slot, hdrBytes, aN]; omega_arith),
    f.wv_eq (by mp_disj) (by simp only [slot, hdrBytes, aN]; omega_arith)⟩

/-- `montPrep`: `-N⁻¹`, `R² mod N`, `R mod N` and `N − R mod N`. -/
theorem montPrep_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w) (hw4 : 4 ≤ w)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs (montPrep M.mm)) s fun t => Ws t B Z w ∧
      ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aN) w = N ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      Frm B (mpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  have hZ16 : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hZ8 : slot w 8 ≤ Z := h.good.2
  have hw2 := h.w2
  have hw' : w < 2 ^ 31 := by omega_arith
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hNlt : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  have hN1 : 1 < N := by
    have : 2 ≤ 2 ^ (64 * (w - 1)) := by
      rw [show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega_arith, Nat.pow_succ]
      have := Nat.two_pow_pos (64 * (w - 1) - 1); omega_arith
    omega_arith
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem B (slot w aN) 1 (w - 1)
    rw [show 1 + (w - 1) = w by omega_arith, hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega_arith
  simp only [montPrep, List.append_assoc]
  refine wp_seqs_append (a := [_, _]) (by simp) (by simp [r2Steps]) ?_
  simp only [seqs]
  -- `-N⁻¹`, and 1.
  refine WP.seq (WP.mono (msHead_ok h hodd0) fun s₁ ⟨⟨hinv₁, hm₁, h12₁, h9₁, h13₁⟩, k₁⟩ => ?_)
  obtain ⟨mi, hmi⟩ : ∃ mi, word s₁.mem B (8 * sMinv) = mi := ⟨_, rfl⟩
  rw [hmi] at hinv₁ hm₁
  have o₁ : Outside B (8 * sMinv) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega_arith)
  have f₁ : Frm B (mpRanges w) s.mem s₁.mem := Frm.of_outside o₁ (by simp [mpRanges])
  have h₁ : Ws s₁ B Z w := h.congr' f₁ (mpRanges_kmut w) k₁ (by decide)
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [o₁.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega_arith) (by simp only [slot, hdrBytes, aN]; omega_arith)]; exact hn
  have hw₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) :=
    o₁.word (by simp only [slot, hdrBytes, aN, sMinv]; omega_arith) (by simp only [slot, hdrBytes, aN]; omega_arith)
  rw [← hw₁] at hinv₁
  have g₁ : Good s₁ B Z w mi := hmi ▸ h₁.good.1
  refine WP.mono (setWord_ok g₁.scr g₁.x0 g₁.hdr hZ8 h12₁ hw' (o := aOne) (by decide) (i := 0) (by omega_arith)
    (by rw [h13₁]; rfl)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_
  rw [h9₁] at hv₂
  have F₂ : Frm B (mpTail w) s₁.mem s₂.mem := Frm.of_outside o₂ (by simp [mpTail])
  have h₂ : Ws s₂ B Z w := h₁.congr' F₂ (mpTail_kmut w) k₂ (by decide)
  obtain ⟨e₂, w₂, n₂⟩ := mp_fix F₂ hnw hZ
  have g₂ : Good s₂ B Z w mi := by have := h₂.good.1; rwa [e₂, hmi] at this
  -- `R² mod N`.
  refine wp_seqs_append (by simp [r2Steps]) (by simp) ?_
  refine WP.mono (r2_ok M g₂ hZ8 (by omega_arith) (by omega_arith) (n₂.trans hn₁) (by rw [w₂]; exact hinv₁) hodd hlo)
    fun s₃ ⟨g₃, hlt₃, hr₃, fr₃, k₃⟩ => ?_
  have F₃ : Frm B (mpTail w) s₁.mem s₃.mem := F₂.trans (fr₃.mono (by simp [r2Ranges, mpTail]))
  have k13 := k₂.trans k₃
  have h₃ : Ws s₃ B Z w := h₁.congr' F₃ (mpTail_kmut w) k13 (by decide)
  obtain ⟨e₃, w₃, n₃⟩ := mp_fix F₃ hnw hZ
  have hR2₃ : wv s₃.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [← hr₃, Nat.mod_eq_of_lt hlt₃]
  have hone₃ : wv s₃.mem B (slot w aOne) w = 1 := by
    rw [fr₃.wv_eq (by mp_disj) (by simp only [slot, hdrBytes, aOne]; omega_arith), hv₂]; rfl
  -- `R mod N`.
  refine wp_seqs_append (by simp) (by simp [subA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (M.mm_ok g₃ hZ8 (by omega_arith) hw' (o := aY) (a := aR2) (b := aOne) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [w₃]; exact hinv₁)
    (by rw [hone₃, n₃, hn₁]; exact hN1)) fun s₄ ⟨g₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_)
  rw [n₃, hn₁, hR2₃, hone₃] at hy₄
  rw [n₃, hn₁] at hlt₄
  have hY : wv s₄.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt₄]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy₄, Nat.mul_one, Nat.mod_mod]
  have fa₄ : Frm B (mpTail w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [mpTail])
  have F₄ : Frm B (mpTail w) s₁.mem s₄.mem := F₃.trans fa₄
  have k14 := k13.trans k₄
  have h₄ : Ws s₄ B Z w := h₁.congr' F₄ (mpTail_kmut w) k14 (by decide)
  have hR2₄ : wv s₄.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) (by omega_arith)]; exact hR2₃
  -- `[aR1] := R mod N`.
  refine WP.mono (copyA_ok h₄ (o := aR1) (a := aY) (by decide) (by decide) (by decide))
    fun s₅ ⟨hv₅, o₅, _, _, k₅⟩ => ?_
  rw [hY] at hv₅
  have fo₅ : Frm B (mpTail w) s₄.mem s₅.mem :=
    Frm.of_outside (o₅.mono (o' := slot w aR1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp [mpTail])
  have F₅ : Frm B (mpTail w) s₁.mem s₅.mem := F₄.trans fo₅
  have k15 := k14.trans k₅
  have h₅ : Ws s₅ B Z w := h₁.congr' F₅ (mpTail_kmut w) k15 (by decide)
  obtain ⟨e₅, w₅, n₅⟩ := mp_fix F₅ hnw hZ
  have hR2₅ : wv s₅.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [o₅.wv (by simp only [slot, hdrBytes, aR1, aR2]; omega_arith) (by simp only [slot, hdrBytes, aR2]; omega_arith)]; exact hR2₄
  -- `[aRm1] := N − R mod N`.
  refine WP.mono (subA_ok h₅ (o := aRm1) (a := aN) (b := aR1) (by decide) (by decide) (by decide) (.inr (by decide))
    (by decide)) fun t ⟨hv₆, o₆, _, _, _, k₆⟩ => ?_
  rw [hv₅, n₅, hn₁] at hv₆
  have hRm₆ : wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N := by
    have hx := wv_lt t.mem B (slot w aRm1) w
    have hm := Nat.mod_lt (2 ^ (64 * w)) (show 0 < N by omega_arith)
    cases hb : (!t.c) <;> rw [hb] at hv₆ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero] at hv₆ <;> omega_arith
  have fo₆ : Frm B (mpTail w) s₅.mem t.mem :=
    Frm.of_outside (o₆.mono (o' := slot w aRm1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp [mpTail])
  have F₆ : Frm B (mpTail w) s₁.mem t.mem := F₅.trans fo₆
  have k16 := k15.trans k₆
  obtain ⟨e₆, w₆, n₆⟩ := mp_fix F₆ hnw hZ
  refine ⟨h₁.congr' F₆ (mpTail_kmut w) k16 (by decide), by rw [w₆, e₆, hmi]; exact hinv₁, n₆.trans hn₁,
    ?_, ?_, hRm₆, f₁.trans (F₆.mono fun r hr => List.mem_cons_of_mem _ hr), (k₁.trans k16).mono (by decide)⟩
  · rw [o₆.wv (by simp only [slot, hdrBytes, aRm1, aR2]; omega_arith) (by simp only [slot, hdrBytes, aR2]; omega_arith)]
    exact hR2₅
  · rw [o₆.wv (by simp only [slot, hdrBytes, aRm1, aR1]; omega_arith) (by simp only [slot, hdrBytes, aR1]; omega_arith)]
    exact hv₅

end VG.Proof.Ffdh.AArch64.ParameterCandidate
