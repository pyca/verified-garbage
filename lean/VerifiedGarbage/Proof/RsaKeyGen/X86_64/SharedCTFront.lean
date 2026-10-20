module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedKMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTFront
import VerifiedGarbage.Proof.Framework.Omega

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
