module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedRanges
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTCode
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedKMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTFront

/-! ### `RsaKeyGen.X86_64.SharedCTTail`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.SharedCTResult`, which only this module used -/

section

/-! # Reuse the existing result routine's constant-time proof -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The result routine needs the final context and three public header
words. Its existential starting memory can be the final memory: it does
not use the history of the loop's workspace or private stack writes. -/
private theorem result_context {a : SharedLPub} {s : State} (h : SharedLoopEnd a s) :
    LoopEnd a.toLPub s := by
  obtain ⟨hk, hd, mi, c, r, s₀, res, ⟨hctx, h0, h1, hf, hkeep⟩, hS, hrl, ho, hu, hl, hw, henv⟩ := h
  obtain ⟨bm, hc⟩ := hctx
  have hh {k : Nat} (h32 : k < 32)
      (hdj : ∀ r ∈ sharedRoundRanges a.p.w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) :
      word s.mem a.p.B (8 * k) = word s₀.mem a.p.B (8 * k) :=
    SharedFrame.word hf henv hdj (by
      have := hdr_lt_slot a.p.w 28 h32
      have := a.z28
      omega_arith) hc.good.scr.nowrap
  let u : State := { s₀ with mem := s.mem }
  refine ⟨hk, hd, mi, c, r, u, res, ⟨⟨bm, hc⟩, h0, h1, Frm.refl _ _ _, hkeep⟩,
    hS, hrl, ?_, ?_, ?_, hw⟩
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans ho
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans hu
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans hl

theorem sharedResult_ct : RelCT isa (Two SharedLoopEnd) mrResult fun _ _ => True :=
  two_map SharedLPub.toLPub (fun _ _ h => result_context h) mrResult_ct

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # Constant time of setup and the callable RSA witness loop -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf)

structure SharedTPub extends TPub where
  sp : Addr
  z28 : slot w 28 ≤ Z

abbrev SharedTPub.lp (q : SharedTPub) : SharedLPub := ⟨q.toTPub.lp, q.sp, q.z28⟩

def SharedMsPre (q : SharedTPub) (s : State) : Prop :=
  MsPre q.toTPub s ∧ SharedEnv q.B q.Z q.sp s

def SharedMrPre0 (a : SharedLPub) (s : State) : Prop :=
  MrPre0 a.toLPub s ∧ SharedEnv a.p.B a.p.Z a.sp s

private theorem setup_run (M : Mont) {q : TPub} {s : State} (h : MsPre q s) :
    ∃ t s', Exec isa (seqs (montSetup M.mm)) s t s' := by
  obtain ⟨⟨-, -, hd, -⟩, -, mi, c, r, hg, hn, hsh, -⟩ := h
  obtain ⟨hodd, hlo, -⟩ := hsh
  have htop : 2 ^ (64 * q.w - 1) ≤ c := by
    have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; have := hd.w4; omega_arith
    omega_arith
  obtain ⟨t, s', he, -⟩ := montSetup_ok M hg hd.z hd.x hd.w4 hd.w64 hn hodd htop
  exact ⟨t, s', he⟩

private theorem setup_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) : RelCT isa (Two SharedMsPre) (seqs (montSetup mm))
    (Two fun q : SharedTPub => SharedMrPre0 q.lp) := by
  refine two_post ?_ ?_
  · refine RelCT.of_inline (montSetup_inlineOk hmc.ok) ?_ ?_ ?_ ?_
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      rw [hmc.montSetup]
      exact ⟨setup_run M h₁.1, setup_run M h₂.1⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact ⟨h₁.2.hole_clear, h₂.2.hole_clear⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact h₁.2.rsp.trans h₂.2.rsp.symm
    · rw [hmc.montSetup]
      exact (two_map SharedTPub.toTPub (fun _ _ h => h.1) (montSetup_ct M)).mono
        (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro q s ⟨⟨⟨hk, hw, hd, -⟩, hrl, mi, c, r, hg, hn, hsh, hO, hU, hR, hK, hRL, hUs, hsrc, hrlen, hrk, hS⟩, henv⟩
    obtain ⟨hodd, hlo, hhi⟩ := hsh
    have hw4 := hd.w4
    have hnw := hg.scr.nowrap
    have htop : 2 ^ (64 * q.w - 1) ≤ c := by
      have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
      omega_arith
    refine WP.mono (montSetup_call_ok M hmc henv hg hd.z hd.x hw4 hd.w64 hn hodd htop)
      fun t ⟨mi', hg', hinv, hr2, hr1, hrm1, hchk, hf, k⟩ => ?_
    have e : ∀ x, x = kOut ∨ x = kUsedP ∨ x = kRand ∨ x = kLen ∨ x = kRandLen ∨ x = kUsed →
        word t.mem q.B (8 * x) = word s.mem q.B (8 * x) := fun x hx => SharedFrame.word hf henv (msRanges_hdr _ x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hx)) (by
          have := hd.z
          have hk32 : x < 32 := by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          have := hdr_lt_slot q.w 8 hk32
          omega_arith) hnw
    have hn' : wv t.mem q.B (slot q.w aN) q.w = c := by
      rw [SharedFrame.array hf henv (d := slot q.w aN) (k := q.w) (by simp only [msRanges]; rng_disj)
        (by have := slot_le (w := q.w) (show aN < 8 by decide); have := hd.z; omega_arith) hnw]; exact hn
    have hle : ∀ r ∈ msRanges q.w, r.1 + r.2 ≤ q.Z := fun r hr => by
      have : r.1 + r.2 ≤ slot q.w aRm1 + 8 * (q.w + 2) := by revert r hr; simp only [msRanges]; rng_le
      have := hd.x; omega_arith
    have hc1 : 1 < c := by have := Nat.two_pow_pos (64 * q.w - 2); omega_arith
    have hch : Proof.RsaKeyGen.checksW q.w < 2 ^ 62 := by
      unfold Proof.RsaKeyGen.checksW; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> decide
    exact ⟨⟨hk, ⟨hg'.rdi, k.2.2.trans hw, fun _ he => absurd he List.not_mem_nil⟩, hd.mr, hch, hrl, mi', c,
      wv t.mem q.B (slot q.w aB) q.w, r, ⟨hg', hinv, hn', rfl, hr1, hrm1⟩, hr2, hc1, ⟨hodd, hlo, hhi⟩,
      by rw [e _ (Or.inl rfl)]; exact hO, by rw [e _ (Or.inr (Or.inl rfl))]; exact hU,
      by rw [e _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hR, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hK,
      by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hRL, hrlen, hchk,
      hsrc.shared henv hf hle k, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]; exact hUs,
      Nat.le_refl _, hrk, hS⟩, henv.kept k (by decide)⟩

private theorem exponent_ct : RelCT isa (Two SharedMrPre0) (seqs expSetup) (Two SharedMrPre) := by
  refine two_post ?_ ?_
  · exact (two_map SharedLPub.toLPub (fun _ _ h => h.1) expSetup_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro a s ⟨h, henv⟩
    have ht := expSetup_pre h
    obtain ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, hr2, hc1, hsh, _⟩ := h
    refine WP.mono (WP.and' ht (WP.mono (expSetup_ok hc.good hd hc.n hsh.1 hc1)
      (fun t ⟨_, _, _, k⟩ => henv.kept k (by decide)))) ?_
    rintro t ⟨⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, he, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC,
      hsrc, hU, hu1, hu2, hS⟩, henv⟩
    exact ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, he, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC,
      hsrc, hU, hu1, hu2, hS, henv⟩

theorem sharedTail_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedMsPre)
      (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult]))
      (fun _ _ => True) :=
  RelCT.seqs_app (by simp [montSetup]) (List.cons_ne_nil _ _)
    (RelCT.seq (RelCT.seqs_app (by simp [montSetup]) (by simp [millerRabinWith])
      (RelCT.seq (RelCT.seqs_app (by simp [montSetup]) (by simp [expSetup, lowWord])
        (RelCT.seq (setup_ct M hmc) (two_map SharedTPub.lp (fun _ _ h => h) exponent_ct)))
        (sharedMillerRabin_ct M hmc R))) sharedResult_ct)

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # Public candidate checks before the callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

structure SharedFPub extends FPub where
  sp : Addr
  z28 : slot w 28 ≤ Z

abbrev SharedFPub.tp (q : SharedFPub) : SharedTPub := ⟨q.toFPub.tp, q.sp, q.z28⟩

def SharedKSt (q : SharedFPub) (s : State) : Prop :=
  KSt q.toFPub s ∧ SharedEnv q.B q.Z q.sp s

def SharedK0 (q : SharedFPub) (s : State) : Prop :=
  K0 q.toFPub s ∧ SharedEnv q.B q.Z q.sp s

private theorem close_ct : RelCT isa (Two SharedKSt) (seqs closeCheck) fun _ _ => True :=
  two_map SharedFPub.toFPub (fun _ _ h => h.1) closeCheck_ct

private theorem close_stage {q : SharedFPub} {s : State} (h : SharedKSt q s) :
    WP isa (seqs closeCheck) s fun t => SharedKSt q t ∧ t.zf = some (!q.sch.close) :=
  WP.mono (WP.keep mmRegs (closeStage_ok h.1) rfl) fun _ ⟨ht, hk⟩ =>
    ⟨⟨ht.1, h.2.kept hk (by decide)⟩, ht.2⟩

private theorem trial_stage {q : SharedFPub} {s : State} (h : SharedKSt q s) (hcl : q.sch.close = false) :
    WP isa (seqs trial) s fun t => SharedKSt q t ∧ t.zf = some (!q.sch.comp) :=
  WP.mono (WP.keep mmRegs (trialStage_ok h.1 hcl) (by decide +kernel)) fun _ ⟨ht, hk⟩ =>
    ⟨⟨ht.1, h.2.kept hk (by decide)⟩, ht.2⟩

private theorem gcd_stage {q : SharedFPub} {s : State} (h : SharedKSt q s)
    (hcl : q.sch.close = false) (hco : q.sch.comp = false) :
    WP isa (seqs gcdCheck) s fun t => SharedKSt q t ∧ t.zf = some (!q.sch.gbad) :=
  WP.mono (WP.keep mmRegs (gcdStage_ok h.1 hcl hco) rfl) fun _ ⟨ht, hk⟩ =>
    ⟨⟨ht.1, h.2.kept hk (by decide)⟩, ht.2⟩

private theorem tail_pre {q : SharedFPub} {s : State} (h : SharedKSt q s)
    (hcl : q.sch.close = false) (hco : q.sch.comp = false) (hg : q.sch.gbad = false) : SharedMsPre q.tp s :=
  ⟨tailPre h.1 hcl hco hg, h.2⟩

private theorem fin2_ct {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (finUsed 2) (fun _ _ => True) :=
  (finUsed2_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

private theorem fin3_ct {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (finUsed 3) (fun _ _ => True) :=
  (finUsed3_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

private theorem trial_ct' {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (seqs trial) (fun _ _ => True) :=
  (trial_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

private theorem gcd_ct {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (seqs gcdCheck) (fun _ _ => True) :=
  (gcdCheck_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

theorem sharedAfterLoad_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedKSt) (seqs (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
    ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
      ([.ite .ne (finUsed 3) (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) fun _ _ => True := by
  refine RelCT.seqs_app (by simp [closeCheck]) (by simp) (RelCT.seq (R := Two fun q s => SharedKSt q s ∧
    s.zf = some (!q.sch.close)) (two_post close_ct fun _ _ h => close_stage h) ?_)
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) (fin2_ct fun _ _ h => h.1.1) ?_
  refine RelCT.seqs_app (by simp [trial]) (by simp) (RelCT.seq (R := Two fun q s => (SharedKSt q s ∧
    s.zf = some (!q.sch.comp)) ∧ q.sch.close = false) (two_post (trial_ct' fun _ _ h => h.1.1) fun q s h => ?_) ?_)
  · have hcl := ne_false h.1.2 h.2
    exact WP.mono (trial_stage h.1.1 hcl) fun t ht => ⟨ht, hcl⟩
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) (fin3_ct fun _ _ h => h.1.1.1) ?_
  refine RelCT.seqs_app (by simp [gcdCheck, loadE]) (by simp) (RelCT.seq (R := Two fun q s => (SharedKSt q s ∧
    s.zf = some (!q.sch.gbad)) ∧ q.sch.close = false ∧ q.sch.comp = false)
      (two_post (gcd_ct fun _ _ h => h.1.1.1) fun q s h => ?_) ?_)
  · have hco := ne_false h.1.1.2 h.2
    exact WP.mono (gcd_stage h.1.1.1 h.1.2 hco) fun t ht => ⟨ht, h.1.2, hco⟩
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) (fin3_ct fun _ _ h => h.1.1.1) ?_
  refine (sharedTail_ct M hmc R).mono (fun _ _ h => two_bind (fun q _ _ h₁ h₂ =>
    ⟨q.tp, tail_pre h₁.1.1.1 h₁.1.2.1 h₁.1.2.2 (ne_false h₁.1.1.2 h₁.2),
      tail_pre h₂.1.1.1 h₂.1.2.1 h₂.1.2.2 (ne_false h₂.1.1.2 h₂.2)⟩) h) fun _ _ h => h

theorem sharedKMain_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedK0) (kMainWith mm R.run) (fun _ _ => True) := by
  rw [kMainWith_eq]
  refine RelCT.seqs_app (by simp [loadC]) (by simp [closeCheck])
    (RelCT.seq (two_post (two_map SharedFPub.toFPub (fun _ _ h => h.1) loadC_ct) ?_) (sharedAfterLoad_ct M hmc R))
  rintro q s ⟨h, henv⟩
  exact WP.mono (WP.keep mmRegs (loadCStage_ok h) rfl) fun _ ⟨ht, hk⟩ => ⟨ht, henv.kept hk (by decide)⟩

end VG.Proof.RsaKeyGen.X86_64
