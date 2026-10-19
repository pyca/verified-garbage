module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Branch
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.LeafCT
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Guards
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Branch
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.LeafCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Guards
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # The key search's loop leaks its public points alone -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

private theorem leaf {Φ : KeyPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → KeyAny q.inputs s) (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂⟩) fun _ _ h => h

private theorem branch_ct (v : RoundImpl) :
    RelCT isa (Two KeysGuard) (branch (attemptCall v)) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leaf (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  refine RelCT.seq (two_piece [.r12, .rsp] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leaf (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece [.r12, .rsp] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leaf (fun _ _ h => h.1.1.any) key_request_ct) ?_
  exact RelCT.seq (two_post ((key_attempt_run_ct v).mono
      (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂⟩) fun _ _ h => h)
    fun q s h => key_attempt_ready v q s (attempt_of_room h)) key_classify_ct

theorem key_iteration_ct (v : RoundImpl) :
    RelCT isa (Two KeyCTL) (iteration (attemptCall v)) (fun _ _ => True) := by
  unfold iteration
  change RelCT isa _ (.seq _ (.seq _ _)) _
  refine RelCT.seq (two_piece [.r12, .rsp] key_ctl_pins (by taint_decide) keys_ready) ?_
  exact RelCT.seq (two_post (branch_ct v) (key_branch_ready v))
    (two_taint [.r12] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_r12 h₁).trans (branch_r12 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then eval .e s = some true ∧ KeyCTL (nextKeyPoint q) s
  else eval .e s = some false

theorem key_ct_step (v : RoundImpl) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (iteration (attemptCall v)) s (KeyCTStep q) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (keys_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (key_branch_ready v q u hu) fun t ht => ?_)
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl, hst⟩, hw⟩ := ht
    rw [← nextKeyPoint_inputs q] at hw
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [KeyCTStep, hc, ite_true]
    exact ⟨hz, original, hzl, hst⟩
  · simp only [KeyBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [KeyCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t

private theorem iteration_pair (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (attemptCall v)) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (iteration (attemptCall v)) s fun t => n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (key_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((key_iteration_ct v).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : keyContinues q
  · simp only [KeyCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2⟩
    have := nextKeyPoint_measure hb
    omega
  · simp only [KeyCTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    rw [h₁] at ht
    cases ht

theorem key_loop_ct (v : RoundImpl) :
    RelCT isa (Two KeyCTL) (.loop (iteration (attemptCall v)) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (attemptCall v)) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86_64.KeyGeneration
