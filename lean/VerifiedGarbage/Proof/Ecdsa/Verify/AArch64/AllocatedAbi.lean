import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedLit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointAbi

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
