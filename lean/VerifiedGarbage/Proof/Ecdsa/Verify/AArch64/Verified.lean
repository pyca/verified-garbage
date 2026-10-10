import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedLit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCacheTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacTiming

/-! ## `JacAbi` -/

section

/-! Production P-256 Jacobian verification preserves the existing ABI and result contract. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jacPre_of {s : State} (h : verifyAArch64.pre s) : VPre p256 s := by
  obtain ⟨h1,h2,h3,h4,h5,h6,held,fit,hdw⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,⟨by rw [h1]; simp,held,fit,hdw _ (by simp)⟩⟩

theorem jacVerify_callsKeep : CallsKeep verifyP256 := by lit_decide

theorem jacVerify_untouched : KeepsUntouched verifyP256 := by lit_decide

theorem jacVerify_keepsV : verifyP256.allInstrs keepsV=true := by lit_decide

theorem jacVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := nafVerify_ok (p256_ok hI) (by decide) hL hT (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jacVerify_callsKeep jacVerify_untouched jacVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointAbi` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_callsKeep : CallsKeep P256Joint.verify := by lit_decide

theorem jointVerify_untouched : KeepsUntouched P256Joint.verify := by lit_decide

theorem jointVerify_keepsV : P256Joint.verify.allInstrs keepsV=true := by lit_decide

theorem jointVerify_a64_of_wp
    (correct : ∀ s,VPre p256 s → WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := correct s (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jointVerify_callsKeep jointVerify_untouched jointVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedAbi` -/

section

/-! The allocated verifier temporarily uses x26–x28 and x30. Its ABI proof
uses the actual save/restore contracts, rather than declaring those registers
syntactically untouched by the optimized arithmetic. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64

private structure OldSafe (c : Prog isa) : Prop where
  untouched : KeepsUntouched c
  callsKeep : CallsKeep c

private theorem callsKeep_seq {a b : Prog isa} : CallsKeep (.seq a b) ↔ CallsKeep a ∧ CallsKeep b := by
  simp only [CallsKeep, Code.calls, List.all_append, Bool.and_eq_true]

private theorem OldSafe.left {a b : Prog isa} (h : OldSafe (.seq a b)) : OldSafe a :=
  ⟨(Bool.and_eq_true_iff.mp h.untouched).1,(callsKeep_seq.mp h.callsKeep).1⟩

private theorem OldSafe.right {a b : Prog isa} (h : OldSafe (.seq a b)) : OldSafe b :=
  ⟨(Bool.and_eq_true_iff.mp h.untouched).2,(callsKeep_seq.mp h.callsKeep).2⟩

private theorem OldSafe.seq {a b : Prog isa} (ha : OldSafe a) (hb : OldSafe b) : OldSafe (.seq a b) :=
  ⟨Bool.and_eq_true_iff.mpr ⟨ha.untouched,hb.untouched⟩,callsKeep_seq.mpr ⟨ha.callsKeep,hb.callsKeep⟩⟩

private theorem oldSafe : OldSafe P256Joint.verify := ⟨jointVerify_untouched,jointVerify_callsKeep⟩

private theorem before_safe : OldSafe (beforeInverse p256) := by
  have h := oldSafe
  exact h.left.seq (h.right.left.seq (h.right.right.left.seq (h.right.right.right.left.seq
    (h.right.right.right.right.left.seq (h.right.right.right.right.right.left.seq ⟨rfl,rfl⟩)))))

private theorem uv_safe : OldSafe (Cfg.uv p256) := oldSafe.right.right.right.right.right.right.right.left

private theorem tail_safe : OldSafe (Cfg.tail p256) := oldSafe.right.right.right.right.right.right.right.right.right

private theorem OldSafe.keeps {c : Prog isa} {s t : State} {tr : List Leak} (h : OldSafe c)
    (he : Exec isa c s tr t) : ∀ r∈VG.Proof.Ecdsa.AArch64.untouched,t.gpr r=s.gpr r :=
  untouched_keep he h.callsKeep h.untouched

 theorem allocatedVerify_keepsV : P256Allocated.verify.allInstrs keepsV=true := by lit_decide

/-- Actual restoration, together with the existing saved-register result, suffices for the ABI. -/
theorem allocated_abiPreserved_of {s t : State} {tr : List Leak}
    (he : Exec isa P256Allocated.verify s tr t)
    (hsv : ∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r)
    (hu : ∀ r∈untouched,t.gpr r=s.gpr r) : abiPreserved s t := by
  refine ⟨fun r hr => ?_,Exec.sp he,Exec.preservedV he allocatedVerify_keepsV⟩
  by_cases hh : r∈untouched
  · exact hu r hh
  · apply hsv r
    revert hh
    revert r
    decide

/-- Compose the two restored arithmetic stages with the unchanged surrounding code. -/
theorem allocatedVerify_extra_preserved (hc : CfgOk p256)
    (hprefix : ∀ s,VPre p256 s → WP isa allocatedPrefix s fun t => ∃ g,Mid p256 s (s.gpr .x3) g t)
    (hinverse : ∀ s₀ s,InverseInput p256 s₀ (s₀.gpr .x3) s →
      WP isa P256Allocated.inverse s fun t => ∀ r∈untouched,t.gpr r=s.gpr r)
    (hpoints : ∀ s₀ g s,VPre p256 s₀ → Mid p256 s₀ (s₀.gpr .x3) g s →
      WP isa P256Allocated.points s fun t => ∀ r∈untouched,t.gpr r=s.gpr r)
    {s s' : State} {tr : List Leak} (hp : VPre p256 s)
    (he : Exec isa P256Allocated.verify s tr s') : ∀ r∈untouched,s'.gpr r=s.gpr r := by
  obtain ⟨a,b,tp,tq,tt,ep,eq,et,_⟩ := allocatedVerify_cut he
  obtain ⟨i,j,ti,tj,tu,ei,ej,eu,_⟩ := allocatedPrefix_cut ep
  obtain ⟨_,_,ebi,ib⟩ := beforeInverse_ok hc hp
  obtain ⟨_,rfl⟩ := ei.det ebi
  obtain ⟨_,_,einv,ki⟩ := hinverse s i ib
  obtain ⟨_,rfl⟩ := ej.det einv
  obtain ⟨_,_,em,g,hm⟩ := hprefix s hp
  obtain ⟨_,rfl⟩ := ep.det em
  obtain ⟨_,_,ept,kp⟩ := hpoints s g a hp hm
  obtain ⟨_,rfl⟩ := eq.det ept
  intro r hr
  exact (tail_safe.keeps et r hr).trans ((kp r hr).trans ((uv_safe.keeps eu r hr).trans
    ((ki r hr).trans (before_safe.keeps ei r hr))))

 theorem allocatedVerify_a64_of_wp
    (correct : ∀ s,VPre p256 s → WP isa P256Allocated.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (restored : ∀ {s t : State} {tr : List Leak},VPre p256 s →
      Exec isa P256Allocated.verify s tr t → ∀ r∈untouched,t.gpr r=s.gpr r)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ tr t,Exec isa P256Allocated.verify s tr t ∧ abiPreserved s t ∧ verifyAArch64.post s t := by
  have hp := jacPre_of hs
  obtain ⟨tr,t,he,hsv,hpost⟩ := correct s hp
  exact ⟨tr,t,he,allocated_abiPreserved_of he hsv (restored hp he),hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointCorrect` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_ok (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s : State} (h : VPre p256 s) :
    WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t :=
  verify_of_joint (p256_ok hI) hL P256Joint.points P256Joint.verify rfl
    (by
      intro s₀ base g s hm ht P hp hr
      exact jointPoints_ok (p256_ok hI) hL hT hm ht hp hr) h

theorem jointVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' :=
  jointVerify_a64_of_wp (fun _ hp => jointVerify_ok hL hI hT hp) s hs

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointVerified` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Joint verification satisfies the existing correctness, ABI, and public-input contract. -/
theorem jointVerify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    :
    Verified AArch64.target P256Joint.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,implies.sat⟩
  · obtain ⟨t,s',he,ha,hp⟩ := jointVerify_a64 hL hI hT s (implies.pre _ hs)
    exact ⟨t,s',he,ha,implies.post s s' hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact jointVerify_ct_of_points (p256_ok hI) jointPrefix_ct
      (fun _ _ ps pt => jointPoints_relCT (p256_ok hI) hL hT ps pt) jointTail_ct
      _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂))
      (jacPublic_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `Verified` -/

section

/-!
# Verified Jacobian P-256 verification on AArch64

The Jacobian comb and sparse signed-window multiplications satisfy the existing
verification contract. Table addresses and exceptional-point branches depend
only on the public key, digest and signature declared public by that contract.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Use the public inputs declared by the shared specification directly. -/
theorem verify_ct (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pub verifyP256 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  apply nafVerify_public_ct (p256_ok hI) (by decide) hL hT nafVerify_checks
    _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := jacVerify_a64 hL hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
