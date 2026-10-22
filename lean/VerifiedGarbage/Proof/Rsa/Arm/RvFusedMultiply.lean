module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedScalar
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedDispatch
public import VerifiedGarbage.Proof.Rsa.Arm.RvMont5
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt

/-! Multiplication by a public candidate, sharing the scalar and Montgomery
proofs. Both branches preserve the same live arrays and exponent. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pfusedMultiply (hn : P.n % 2 = 1 ∧ 1 < P.n) {j : Nat} (hj : j < 100)
    (hz : aZ ∈ L) (hN : aN ∈ L) (hx : mX ∈ L) (hg : mG ∈ L)
    (h2 : mBase + 2 ∉ L) (h3 : mBase + 3 ∉ L) (hc : sCand ∈ LS)
    (values : ∀ σ, E σ → A σ aZ = 0 ∧ A σ aN = P.n ∧ A σ mX < P.n ∧
      A σ mG = (j + 2) * Rm P % P.n ∧ V σ sCand = j)
    (wide : ∀ k ∈ LW, ∀ i ∈ RecoverScalar.writes, i / 2 ≠ k)
    (montWide : ∀ k ∈ LW, k ≠ (mBase + 2) / 2 ∧ k ≠ (mBase + iXm) / 2)
    (slots : ∀ d ∈ LS, d + 4 ≤ sC ∨ sC + 4 ≤ d) :
    VP (St P E A L AW LW V LS P.w nArr) multiply
      (St P E (fun σ => upd (A σ) mXm (((j + 2) * A σ mX) % P.n))
        (mXm :: scalarLive L) AW LW V LS P.w nArr) := by
  have pos : 0 < P.n := by omega
  unfold multiply
  refine St.pcandidateIf hj (by decide) (by decide) ⟨_, by taint_decide⟩ hc
    (fun σ e => (values σ e).2.2.2.2) ?_
  by_cases zero : j = 0
  · subst zero
    simp only [↓reduceIte]
    exact St.pscalar VG.Impl.Rsa.Arm.RecoverScalar.twice 2 ⟨_, by taint_decide⟩
      @RecoverScalar.twice_ok hz hN hx (fun σ e =>
        ⟨(values σ e).1, (values σ e).2.1, (values σ e).2.2.1⟩) wide slots
  · simp only [zero, ↓reduceIte]
    refine St.pcandidateIf hj (by decide) (by decide) ⟨_, by taint_decide⟩ hc
      (fun σ e => (values σ e).2.2.2.2) ?_
    by_cases one : j = 1
    · subst one
      simp only [↓reduceIte]
      exact St.pscalar VG.Impl.Rsa.Arm.RecoverScalar.three 3 ⟨_, by taint_decide⟩
        @RecoverScalar.three_ok hz hN hx (fun σ e =>
          ⟨(values σ e).1, (values σ e).2.1, (values σ e).2.2.1⟩) wide slots
    · simp only [one, ↓reduceIte]
      refine (St.pmmul (o := iXm) (a := iX) (b := iG) (by decide) hn.1
        (T := fun σ => ((j + 2) * A σ mX) % P.n) hx hg h2 h3 montWide
        (fun σ e => ?_)).mono (fun _ _ h => h) fun σ s h => h.mono ?_
          (fun k hk => ⟨hk, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
      · obtain ⟨_, _, bound, candidate, _⟩ := values σ e
        refine ⟨bound, ?_, Nat.mod_lt _ pos, ?_⟩
        · change A σ mG < P.n
          rw [candidate]; exact Nat.mod_lt _ pos
        · change (((j + 2) * A σ mX) % P.n) * Rm P % P.n = A σ mX * A σ mG % P.n
          rw [candidate, Nat.mod_mul_mod, Nat.mul_mod_mod]
          congr 1
          ac_rfl
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ⟨by simp only [List.mem_cons]; left; rfl, rfl⟩
        · exact ⟨List.mem_cons_of_mem _ (List.mem_filter.mp hk).1, rfl⟩

end
end VG.Proof.Rsa.Arm.Recover
