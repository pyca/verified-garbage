module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KMain
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-! # RSA candidate checks with a shared Miller–Rabin kernel -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY sCnt)

/-- `kMain`. -/
theorem sharedKMain_ok (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) {s : State} {B : Addr} {Z w : Nat} {op up eP pP rP : Addr} {eB pB r : List Byte}
    (h : MainCtx s B Z w op up eP pP rP eB pB r) :
    WP isa (kMainWith M.mm R.run) s fun t => CandEnd s t op up (8 * w) r
      (VG.Proof.RsaKeyGen.afterDraw (64 * w) (Spec.Rsa.os2ip eB) (Spec.RsaKeyGen.otherPrime pB)
        (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w)))) (r.drop (8 * w))) := by
  have hs := h.scr
  have hnw := hs.nowrap
  have hw4 := h.w4
  have hw64 := h.w64
  have hZ := h.z
  have hrk := h.rk
  have h256 : 8 * 32 ≤ Z := by omega_arith
  have hTZ : slot w aTab + 2048 ≤ Z := by simp only [slot, hdrBytes, aTab]; omega_arith
  have hW : ∀ {rs : List (Nat × Nat)} {m m' : Mem}, Frm B rs m m' → ∀ {i : Nat}, i < 32 →
      (∀ r ∈ rs, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word m' B (8 * i) = word m B (8 * i) :=
    fun f _ hi hd => f.word_eq hd (by omega_arith)
  have hrest : r.length - (r.length - 8 * w) = 8 * w := by omega_arith
  unfold kMainWith
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [loadC]) (by simp [closeCheck]) ?_
  -- The candidate.
  have hsrcr : Src s B Z rP (r.take (8 * w)) :=
    ⟨fun i hi => h.rsrc.rd i (by simp at hi; omega_arith),
      fun i hi => by rw [h.rsrc.val i (by simp at hi; omega_arith), List.getElem_take],
      fun i hi => h.rsrc.out i (by simp at hi; omega_arith)⟩
  refine WP.mono (loadC_ok hs h.x0 hw4 (by omega_arith) hZ h.len h.rand hsrcr (by simp; omega_arith))
    fun s₁ ⟨h₁, hM₁, hc₁, hus₁, f₁, k₁⟩ => ?_
  generalize hcv : Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w))) = c at hc₁ ⊢
  have hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c := hcv ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega_arith) _
  have hgt : 8161 < c := by
    obtain ⟨_, hlo, _⟩ := hsh
    have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  have hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm f₁ (by have := h₁.hZ; k_le)
  have ho₁ := h.ou.congr k₁.wr
  have hP₁ : word s₁.mem B (8 * kP) = pP := (hW f₁ (by decide) (by k_disj)).trans h.p
  have hPl₁ : word s₁.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length := (hW f₁ (by decide) (by k_disj)).trans h.plen
  -- Too close to `p`.
  refine wp_seqs_append (by simp [closeCheck]) (by simp) ?_
  refine WP.mono (closeCheck_ok h₁ hw4 hP₁ hPl₁ h.pl (h.psrc.congrK hin₁ k₁)) fun s₂ ⟨hz₂, h₂, f₂, k₂⟩ => ?_
  rw [hc₁] at hz₂
  have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have hin₂ : InScr B Z s.mem s₂.mem := hin₁.trans (InScr.of_frm f₂ (by have := h₁.hZ; k_le))
  have ho₂ := h.ou.congr k12.wr
  have hk₂ : ∀ {i : Nat}, i < 32 → (∀ r ∈ loadCRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) →
      (∀ r ∈ closeRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word s₂.mem B (8 * i) = word s.mem B (8 * i) :=
    fun hi d₁ d₂ => (hW f₂ hi d₂).trans (hW f₁ hi d₁)
  have hus₂ : word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) := (hW f₂ (by decide) (by k_disj)).trans hus₁
  have hU₂ : word s₂.mem B (8 * kUsedP) = up := (hk₂ (by decide) (by k_disj) (by k_disj)).trans h.usedP
  rw [seqs_one]
  refine WP.ite (Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) c)
    (by rw [eval_nonzero, hz₂, mask_bne]) (fun hcl => ?_) (fun hcl => ?_)
  · refine WP.mono (finUsed_end h₂.scr h₂.x0 h256 (by decide) hus₂ hU₂ ho₂ hin₂ k12) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    rw [hcl]
    simp only [↓reduceIte, CandEnd, List.length_drop]
    rwa [hrest]
  have hc₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [f₂.wv_eq (d := slot w aN) (k := w) (by k_disj) (by have := h₂.hZ; simp only [slot, hdrBytes, aN] at *; omega_arith)]
    exact hc₁
  have hrej : ∀ t, KEnd s t op up (8 * w) 3 (8 * w) none → CandEnd s t op up (8 * w) r
      (some (.rejected, r.drop (8 * w))) := fun t ht => by
    simp only [CandEnd, List.length_drop]
    rwa [hrest]
  -- Trial division.
  refine wp_seqs_append (by simp [trial]) (by simp) ?_
  refine WP.mono (trial_ok h₂ hTZ hw4 hw64) fun s₃ ⟨hz₃, h₃, f₃, k₃⟩ => ?_
  rw [hc₂, VG.Proof.RsaKeyGen.trialAny_eq hgt] at hz₃
  have k13 : Keep mmRegs s s₃ := (k12.trans k₃).mono (by decide)
  have hin₃ : InScr B Z s.mem s₃.mem := hin₂.trans (InScr.of_frm f₃ (by k_le))
  have ho₃ := h.ou.congr k13.wr
  have hk₃ : ∀ {i : Nat}, i < 32 → (∀ r ∈ loadCRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) →
      (∀ r ∈ closeRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word s₃.mem B (8 * i) = word s.mem B (8 * i) :=
    fun hi d₁ d₂ => (hW f₃ hi (by k_disj)).trans (hk₂ hi d₁ d₂)
  have hus₃ : word s₃.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) := (hW f₃ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)).trans hus₂
  rw [seqs_one]
  have hU₃ : word s₃.mem B (8 * kUsedP) = up := (hk₃ (by decide) (by k_disj) (by k_disj)).trans h.usedP
  refine WP.ite (Spec.RsaKeyGen.obviouslyComposite (64 * w) c) (by rw [eval_nonzero, hz₃]) (fun hoc => ?_)
    (fun hoc => ?_)
  · refine WP.mono (finUsed_end h₃.scr h₃.x0 h256 (by decide) hus₃ hU₃ ho₃ hin₃ k13) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and]
    exact hrej t ht
  have hc₃ : wv s₃.mem B (slot w aN) w = c := by
    rw [f₃.wv_eq (d := slot w aN) (k := w) (by k_disj) (by have := h₂.hZ; simp only [slot, hdrBytes, aN] at *; omega_arith)]
    exact hc₂
  -- `gcd(c − 1, e)`.
  refine wp_seqs_append (by simp [gcdCheck]) (by simp) ?_
  refine WP.mono (gcdCheck_ok h₃ (by rw [hc₃]; exact hsh.1) (by rw [hc₃]; omega_arith)
    ((hk₃ (by decide) (by k_disj) (by k_disj)).trans h.e) ((hk₃ (by decide) (by k_disj) (by k_disj)).trans h.elen)
    h.el1 h.el8 (h.esrc.congrK hin₃ k13)) fun s₄ ⟨hz₄, h₄, f₄, k₄⟩ => ?_
  rw [hc₃] at hz₄
  have k14 : Keep mmRegs s s₄ := (k13.trans k₄).mono (by decide)
  have hin₄ : InScr B Z s.mem s₄.mem := hin₃.trans (InScr.of_frm f₄ (by have := h₁.hZ; k_le))
  have ho₄ := h.ou.congr k14.wr
  have hk₄ : ∀ {i : Nat}, 2 ≤ i → i < 32 → (∀ r ∈ loadCRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) →
      (∀ r ∈ closeRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word s₄.mem B (8 * i) = word s.mem B (8 * i) :=
    fun _ hi d₁ d₂ => (hW f₄ hi (by k_disj)).trans (hk₃ hi d₁ d₂)
  have hus₄ : word s₄.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) :=
    (hW f₄ (by decide) (by k_disj)).trans ((hW f₃ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)).trans hus₂)
  have hU₄ : word s₄.mem B (8 * kUsedP) = up := (hk₄ (by decide) (by decide) (by k_disj) (by k_disj)).trans h.usedP
  rw [seqs_one]
  refine WP.ite (!decide (Nat.gcd (c - 1) (Spec.Rsa.os2ip eB) = 1)) (by rw [eval_nonzero, hz₄]) (fun hgc => ?_)
    (fun hgc => ?_)
  · refine WP.mono (finUsed_end h₄.scr h₄.x0 h256 (by decide) hus₄ hU₄ ho₄ hin₄ k14) fun t ht => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hgc
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq]
    exact hrej t ht
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hgc
  have hc₄ : wv s₄.mem B (slot w aN) w = c := by
    rw [f₄.wv_eq (d := slot w aN) (k := w) (by k_disj) (by have := h₂.hZ; simp only [slot, hdrBytes, aN] at *; omega_arith)]
    exact hc₃
  have hM₄ : word s₄.mem B (8 * Public.sMask) = mask true :=
    (hW f₄ (by decide) (by k_disj)).trans ((hW f₃ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)).trans ((hW f₂ (by decide) (by k_disj)).trans hM₁))
  refine WP.mono (sharedTail_ok M R h₄ hw4 hw64 (by simp only [slot, hdrBytes, aE]; omega_arith) hc₄ hsh ho₄ ((hk₄ (by decide) (by decide) (by k_disj) (by k_disj)).trans h.out)
    ((hk₄ (by decide) (by decide) (by k_disj) (by k_disj)).trans h.len) hU₄ hM₄
    ((hk₄ (by decide) (by decide) (by k_disj) (by k_disj)).trans h.rand) ((hk₄ (by decide) (by decide) (by k_disj) (by k_disj)).trans h.rlen)
    hus₄ (h.rsrc.congrK hin₄ k14) h.rl hrk) fun t ht => ?_
  have hout := outBytes_inScr hin₄ h.ou.outZ
  have kk : Keep (.x0 :: mmRegs) s s₄ := k14.mono (by decide)
  unfold VG.Proof.RsaKeyGen.afterDraw
  simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_self_eq_true]
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact KEnd.trans_pre ht hout kk
  · rw [hp] at ht
    cases b
    · exact KEnd.trans_pre ht hout kk
    · exact KEnd.trans_pre ht hout kk

end VG.Proof.RsaKeyGen.AArch64
