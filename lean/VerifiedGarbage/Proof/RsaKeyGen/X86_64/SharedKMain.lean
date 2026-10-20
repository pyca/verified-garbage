module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedTail
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCall
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedEnd
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE

/-! # All candidate checks followed by the shared prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

theorem kMainWith_eq (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : kMainWith mul body =
    seqs (loadC ++ (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
      ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
        ([.ite .ne (finUsed 3) (seqs (montSetup mul ++ expSetup ++ millerRabinWith mul body ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) := by
  unfold kMainWith; rw [List.append_assoc]

/-- `kMain`. -/
theorem sharedKMain_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B sp : Addr} {Z w : Nat} {op up eP pP rP : Addr} {eB pB r : List Byte}
    (henv : SharedEnv B Z sp s) (hZ28 : slot w 28 ≤ Z) (h : MainCtx s B Z (8 * w) op up eP pP rP eB pB r) :
    WP isa (kMainWith mm R.run) s fun t => SharedCandEnd s t B sp Z op up (8 * w) r
      (VG.Proof.RsaKeyGen.afterDraw (64 * w) (Spec.Rsa.os2ip eB) (Spec.RsaKeyGen.otherPrime pB)
        (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w)))) (r.drop (8 * w))) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hk1 := h.k1
  have hk2 := h.k2
  have hw8 : 8 * w / 8 = w := by omega_arith
  have hTZ := h.z
  rw [hw8] at hTZ
  have hZ : slot w 8 ≤ Z := by unfold slot aTab at *; omega_arith
  have hl8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  rw [kMainWith_eq]
  refine wp_seqs_append (by simp [loadC]) (by simp [closeCheck]) ?_
  -- The candidate.
  have hsrcr : Src s B Z rP (r.take (8 * w)) := by
    have := VG.Proof.RsaKeyGen.X86_64.Src.seg h.rsrc (a := 0) (n := 8 * w) (by have := h.rk; omega_arith)
    rwa [seg_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  refine WP.mono (loadC_ok hs h.rdi (by rw [hw8]; exact hZ) (by omega_arith) (by omega_arith) (by omega_arith) h.len h.rand hsrcr
    (by simp; have := h.rk; omega_arith)) fun s₁ ⟨hc₁, hus₁, hsw₁, harr₁, hf₁, hdi₁, h12₁, k₁⟩ => ?_
  rw [hw8, show 8 * (8 * w) = 64 * w by omega_arith] at hc₁
  rw [hw8] at hsw₁ harr₁ hf₁
  generalize hcv : Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w))) = c at hc₁ ⊢
  have hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c := hcv ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega_arith) _
  have hg₁ : Good s₁ B Z w (word s₁.mem B (8 * sMinv)) := ⟨hs.congr k₁.2.2, hdi₁, ⟨hsw₁, rfl, harr₁⟩⟩
  have hh₁ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have hi32 : i < 32 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine hf₁.word_eq ?_ (by omega_arith)
    simp only [loadCRanges]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
  have hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm hf₁ (by simp only [loadCRanges]; rng_le)
  have hsv₁ : ∀ i < 6, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf₁.word_eq (fun r hr => Or.inl (by revert r hr; simp only [loadCRanges]; rng_le)) (by omega_arith)
  have st₁ : (∀ i ≤ 25, word s₁.mem B (8 * i) = word s₁.mem B (8 * i)) ∧ InScr B Z s₁.mem s₁.mem :=
    ⟨fun _ _ => rfl, InScr.refl _ _ _⟩
  have ho₁ := h.ou.congr k₁.2.2
  -- Too close to `p`.
  refine wp_seqs_append (by simp [closeCheck]) (by simp) ?_
  refine WP.mono (closeCheck_ok hg₁ hZ (by omega_arith) (by omega_arith) (by rw [hh₁ (by simp)]; exact h.p)
    (by rw [hh₁ (by simp)]; exact h.len) (by rw [hh₁ (by simp)]; exact h.plen) h.pl (h.psrc.congrK hin₁ k₁))
    fun s₂ ⟨hz₂, hg₂, hf₂, k₂⟩ => ?_
  rw [hc₁] at hz₂
  have st₂ := stage hf₂ (by simp only [closeRanges]; rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; simp only [closeRanges]; rng_le
    omega_arith) st₁
  have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have hsv₂ : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₂.1 i (by omega_arith)).trans (hsv₁ i hi)
  have hin₂ : InScr B Z s.mem s₂.mem := hin₁.trans st₂.2
  have hk₂ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₂.1 i this, hh₁ hi]
  have hu₂ : word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) := by rw [st₂.1 kUsed (by decide), hus₁]
  refine WP.ite (Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) c) (by simp [eval, hz₂])
    (fun hcl => ?_) (fun hcl => ?_)
  · refine WP.mono (sharedFinUsed_end (sp := sp) hg₂.scr hg₂.rdi hl8 (by decide) hu₂ (by rw [hk₂ (by simp)]; exact h.usedP)
      (h.ou.congr k12.2.2) hsv₂ hin₂ k12) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    rw [hcl]
    simp only [↓reduceIte, SharedCandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega_arith]
  have hc₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [hf₂.wv_eq (d := slot w aN) (k := w) (by simp only [closeRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₁
  have hgt : 8161 < c := by
    obtain ⟨_, hlo, _⟩ := hsh
    have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  have hend : ∀ {sX : State} {mi : BitVec 64}, Good sX B Z w mi → Keep mmRegs s sX →
      (∀ i ≤ 25, word sX.mem B (8 * i) = word s₁.mem B (8 * i)) → InScr B Z s₁.mem sX.mem →
      WP isa (finUsed 3) sX fun t => SharedKEnd s t B sp Z op up (8 * w) 3 (8 * w) none := by
    intro sX mi hgX kX hX hinX
    exact sharedFinUsed_end (sp := sp) hgX.scr hgX.rdi hl8 (by decide) (by rw [hX kUsed (by decide), hus₁])
      (by rw [hX kUsedP (by decide), hh₁ (by simp)]; exact h.usedP) (h.ou.congr kX.2.2)
      (fun i hi => (hX i (by omega_arith)).trans (hsv₁ i hi)) (hin₁.trans hinX) kX
  have hrej : ∀ t, SharedKEnd s t B sp Z op up (8 * w) 3 (8 * w) none → SharedCandEnd s t B sp Z op up (8 * w) r
      (some (.rejected, r.drop (8 * w))) := fun t ht => by
    simp only [SharedCandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega_arith]
  -- Trial division.
  refine wp_seqs_append (by simp [trial]) (by simp) ?_
  refine WP.mono (trial_ok hg₂ hZ hTZ (by omega_arith) (by omega_arith)) fun s₃ ⟨hz₃, hg₃, hf₃, k₃⟩ => ?_
  rw [hc₂, trialAny_eq hgt] at hz₃
  have st₃ := stage hf₃ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w aTab + 2048 := by revert r hr; rng_le
    omega_arith) st₂
  have k13 : Keep mmRegs s s₃ := (k12.trans k₃).mono (by decide)
  refine WP.ite (Spec.RsaKeyGen.obviouslyComposite (64 * w) c) (by simp [eval, hz₃]) (fun hoc => ?_) (fun hoc => ?_)
  · refine WP.mono (hend hg₃ k13 st₃.1 st₃.2) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and]
    exact hrej t ht
  have hc₃ : wv s₃.mem B (slot w aN) w = c := by
    rw [hf₃.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₂
  have hk₃ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₃.1 i this, hh₁ hi]
  -- `gcd(c − 1, e)`.
  refine wp_seqs_append (by simp [gcdCheck, loadE]) (by simp) ?_
  refine WP.mono (gcdCheck_ok hg₃ hZ (by omega_arith) (by omega_arith) (by rw [hc₃]; exact hsh.1)
    (by rw [hc₃]; omega_arith) (by rw [hk₃ (by simp)]; exact h.e) (by rw [hk₃ (by simp)]; exact h.elen) h.el1 h.el8
    (h.esrc.congrK (hin₁.trans st₃.2) k13)) fun s₄ ⟨hz₄, hg₄, hf₄, k₄⟩ => ?_
  rw [hc₃] at hz₄
  have st₄ := stage hf₄ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; rng_le
    omega_arith) st₃
  have k14 : Keep mmRegs s s₄ := (k13.trans k₄).mono (by decide)
  refine WP.ite (!decide (Nat.gcd (c - 1) (Spec.Rsa.os2ip eB) = 1)) (by simp [eval, hz₄]) (fun hgc => ?_)
    (fun hgc => ?_)
  · refine WP.mono (hend hg₄ k14 st₄.1 st₄.2) fun t ht => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hgc
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq]
    exact hrej t ht
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hgc
  have hc₄ : wv s₄.mem B (slot w aN) w = c := by
    rw [hf₄.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₃
  have hk₄ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₄.1 i this, hh₁ hi]
  have hXZ := h.zx
  rw [hw8] at hXZ
  refine WP.mono (sharedKTail_ok M hmc R (henv.kept k14 (by decide)) hZ28 hg₄ hZ hXZ (by omega_arith) (by omega_arith) hc₄ hsh (h.ou.congr k14.2.2)
    (by rw [hk₄ (by simp)]; exact h.out) (by rw [hk₄ (by simp)]; exact h.len) (by rw [hk₄ (by simp)]; exact h.usedP)
    (by rw [hk₄ (by simp)]; exact h.rand) (by rw [hk₄ (by simp)]; exact h.rlen)
    (by rw [st₄.1 kUsed (by decide), hus₁]) (h.rsrc.congrK (hin₁.trans st₄.2) k14) h.rl h.rk) fun t ht => ?_
  have hlo : ∀ i < 6, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₄.1 i (by omega_arith)).trans (hsv₁ i hi)
  have hhi : ∀ x, Z ≤ ofs B x → s₄.mem x = s.mem x := fun x hx => ((hin₁.trans st₄.2) x hx)
  unfold VG.Proof.RsaKeyGen.afterDraw
  simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_self_eq_true]
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14
  · rw [hp] at ht
    cases b
    · exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14
    · exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14

end VG.Proof.RsaKeyGen.X86_64
