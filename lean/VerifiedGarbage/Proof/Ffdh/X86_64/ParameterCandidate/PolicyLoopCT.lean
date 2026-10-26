module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyStep
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: timing of the uniform round policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64

private def policyInv (n : Nat) : State → State → Prop :=
  Two fun d s => d.i + n = d.checks ∧ PolicyBefore d s

private theorem checks_bound {d : PolicyPublic} {s : State} (h : PolicyBefore d s) : d.checks < 2 ^ 31 := by
  obtain ⟨_, _, _, _, _, _, hc⟩ := h
  exact hc

private theorem policy_step (M : Mont) (K : Kernel) (n : Nat) :
    RelCT isa (policyInv n) (roundBody M.mm K.run) fun s₁ s₂ =>
      isa.eval .e s₁ = isa.eval .e s₂ ∧ (isa.eval .e s₁ = some false → True) ∧
        (isa.eval .e s₁ = some true → ∃ m < n, policyInv m s₁ s₂) := by
  have hct : RelCT isa (policyInv n) (roundBody M.mm K.run)
      (Two fun d s => d.i + n = d.checks ∧ d.checks < 2 ^ 31 ∧ PolicyAfter d s) :=
    two_post (two_map (fun d : PolicyPublic => d) (fun _ _ h => h.2) (roundBody_ct M K))
      (fun d s h => WP.mono (policy_after M K d s h.2) fun _ ht => ⟨h.1, checks_bound h.2, ht⟩)
  refine hct.mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨d, ⟨hsize, hc32, h₁⟩, ⟨_, _, h₂⟩⟩
  obtain ⟨u₁, hu₁, ht₁, _, hi₁, hr₁, hz₁, hc₁, hsp₁, hw₁, hk₁, hroom₁⟩ := h₁
  obtain ⟨u₂, hu₂, ht₂, _, hi₂, hr₂, hz₂, hc₂, hsp₂, hw₂, hk₂, hroom₂⟩ := h₂
  refine ⟨by simp only [eval, hz₁, hz₂], fun _ => trivial, fun hgo => ?_⟩
  have hfour : runStatus d.p d.i d.checks d.sample = 4 := of_decide_eq_true (by
    simpa only [eval, hz₁, Option.some.injEq] using hgo)
  cases he : Spec.Ffdh.drawWitness d.p.N d.bs with
  | none => simp only [PolicyPublic.sample, he, Option.map_none, runStatus] at hfour; contradiction
  | some ar =>
    obtain ⟨a, rest⟩ := ar
    have hsample : d.sample = some a := by simp only [PolicyPublic.sample, he, Option.map_some]
    have hpass : Spec.Ffdh.mrRound d.p.N a = true ∧ d.i + 1 < d.checks := by
      by_cases hp : Spec.Ffdh.mrRound d.p.N a = true
      · by_cases hm : d.i + 1 < d.checks
        · exact ⟨hp, hm⟩
        · simp [runStatus, hsample, hp, passStatus, hm] at hfour
      · have hp' : Spec.Ffdh.mrRound d.p.N a = false := Bool.eq_false_iff.mpr hp
        simp [runStatus, hsample, hp'] at hfour
    have hrest₁ := hr₁ a rest he
    have hrest₂ := hr₂ a rest he
    have heq : u₁ = u₂ := by
      have hl₁ := congrArg List.length hrest₁
      have hl₂ := congrArg List.length hrest₂
      simp only [List.length_drop] at hl₁ hl₂
      omega_using [hl₁, hl₂, hu₁, hu₂]
    subst u₂
    let d' : PolicyPublic := { d with rp := off d.rp u₁, used := d.used + u₁, bs := d.bs.drop u₁, i := d.i + 1 }
    have hidx₁ : word s₁.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 (d.i + 1) := by
      simpa only [runIndex, hsample, hpass.1, ite_true] using hi₁
    have hidx₂ : word s₂.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 (d.i + 1) := by
      simpa only [runIndex, hsample, hpass.1, ite_true] using hi₂
    refine ⟨n - 1, by omega_using [hsize, hpass.2], d', ?_, ?_⟩
    · refine ⟨?_, ⟨⟨ht₁, hw₁, hk₁⟩, hroom₁, hsp₁, hidx₁, hc₁, ?_, hc32⟩⟩
      · change d.i + 1 + (n - 1) = d.checks
        omega_using [hsize, hpass.2]
      · change d.i + 1 < 2 ^ 31
        omega_using [hc32, hpass.2]
    · refine ⟨?_, ⟨⟨ht₂, hw₂, hk₂⟩, hroom₂, hsp₂, hidx₂, hc₂, ?_, hc32⟩⟩
      · change d.i + 1 + (n - 1) = d.checks
        omega_using [hsize, hpass.2]
      · change d.i + 1 < 2 ^ 31
        omega_using [hc32, hpass.2]

theorem policyLoop_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two fun d s => PolicyBefore d s ∧ d.i < d.checks)
      (.loop (roundBody M.mm K.run) .e) fun _ _ => True := by
  rintro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨d, h₁, h₂⟩ e₁ e₂
  exact RelCT.loop policyInv (policy_step M K) (d.checks - d.i) s₁ s₂ tr₁ tr₂ t₁ t₂
    ⟨d, ⟨by omega_using [h₁.2], h₁.1⟩, ⟨by omega_using [h₂.2], h₂.1⟩⟩ e₁ e₂

end VG.Proof.Ffdh.X86_64.ParameterCandidate
