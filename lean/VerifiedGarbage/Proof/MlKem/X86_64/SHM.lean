module

public import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# ML-KEM on x86-64: `Sample4.sampleHM`, the sponge absorbing `m` blocks

`sampleH` (`SHTop.lean`, `SHCT.lean`) with the fourth state absorbing only
the first `m ≤ 3` blocks (`squeezesH'_ok`), stored back as the sponge's
after the `m`-th squeeze (`hsave_ok`), then permuted by the other squeezes
(`sqYs_ok`), which write below the sponge's state; the runs on the first
three seeds do not depend on the fourth state.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.Sha3 (iterF)

/-- The three squeezes, the first `m` absorbing a block, with the sponge's
state stored after the `m`-th. -/
theorem squeezesHM_ok {fast : Bool} {m : Nat} (hm : m ≤ 3) {σ : State} (hp : PreW true σ) {s : State}
    (h : SqY true σ (hst σ 0) 0 0 s) (hr : HR σ s.mem) :
    WP isa (squeezesHM fast m) s fun s' => SqY true σ (iterF (3 - m) (hst σ m)) 0 3 s' ∧ HS σ (hst σ m) s'.mem := by
  unfold squeezesHM
  have h₁ : WP isa (if m = 0 then .block [] else squeezesHM.squeezesH' fast m) s
      fun s' => SqY true σ (hst σ m) 0 m s' := by
    by_cases h0 : m = 0
    · subst h0; rw [ite_eq_left rfl]; exact WP.block_nil h
    · rw [ite_eq_right h0]; exact WP.mono (squeezesH'_ok (by omega) hm hp h hr) fun _ h' => h'.1
  refine WP.seq (WP.mono h₁ fun s₁ q₁ => WP.seq (WP.mono (hsave_ok hp q₁ hm) fun s₂ ⟨q₂, e₂⟩ => ?_))
  by_cases h3 : m = 3
  · subst h3; rw [ite_eq_left rfl]; exact WP.block_nil ⟨q₂, e₂⟩
  · rw [ite_eq_right h3]
    refine WP.mono (sqYs_ok (fast := fast) hp (n := 3 - m) (by omega) (by omega) q₂) fun s' ⟨q', f'⟩ => ?_
    refine ⟨by rwa [show m + (3 - m) = 3 by omega] at q', HS.frame e₂ f' fun r hr => ?_⟩
    rw [List.mem_singleton.mp hr]; exact (low_hs σ).symm

theorem correctHM {fast : Bool} {m : Nat} (hm : m ≤ 3) (σ : State) (hs : (sampleHMKW true m).pre σ) :
    ∃ t s', Exec isa (sampleHM fast m) σ t s' ∧ abiPreserved σ s' ∧ (sampleHMKW true m).post σ s' := by
  have hp := preW_of (w16 := true) hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (startF_ok hp) fun s₁ ⟨h₁, r₁⟩ =>
    WP.seq (WP.mono (hload_ok hp h₁ r₁) fun s₂ ⟨h₂, r₂⟩ =>
      WP.seq (WP.mono (squeezesHM_ok (fast := fast) hm hp h₂ r₂) fun s₃ ⟨h₃, e₃⟩ =>
        run3_ok (fast := fast) hp h₃ e₃)))
  refine ⟨t, s', he, abiPreserved_of_exec ?_ he hF.2, hF.1⟩
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> cases fast <;> decide +kernel

theorem squeezesHM_ct {fast : Bool} {m : Nat} (hm : m ≤ 3) :
    RelCT isa (S4.R4W true fun σ s => SqY true σ (hst σ 0) 0 0 s ∧ HR σ s.mem) (squeezesHM fast m)
      (S4.R4W true fun σ s => SqY true σ (iterF (3 - m) (hst σ m)) 0 3 s ∧ HS σ (hst σ m) s.mem) := by
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezesHM fast m) hc).isSome = true := by
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> cases fast
    all_goals exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := hsq
  exact relInv (fun σ s hp h => squeezesHM_ok (fast := fast) hm (preW_of hp) h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) c)

theorem ctHM {fast : Bool} {m : Nat} (hm : m ≤ 3) :
    ConstantTime isa (sampleHMKW true m).pre (sampleHMKW true m).pub (sampleHM fast m) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq startH_ct (RelCT.seq hload_ct
    (RelCT.seq (squeezesHM_ct (fast := fast) hm)
      (RelCT.seq (tabY_ct (Y := fun σ => iterF (3 - m) (hst σ m)) (Hf := fun σ => hst σ m)) ?_))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

end VG.Proof.MlKem.X86_64.SH
