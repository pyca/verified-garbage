module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFin1
import VerifiedGarbage.Proof.Rsa.RecoverFusedBounds
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
public import VerifiedGarbage.Proof.Rsa.RecoverFused

/-! The fused algorithm supplies the common factor-extraction interface.
The ISA search proof must establish this saved root and success flag. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm

def fusedResult (P : RP) (σ : State) (j : Nat) : Option Nat :=
  if 1 < P.n then
    (VG.Proof.Rsa.Fused.eval P.n (j + 2) (mv P σ)).root
  else none

theorem fusedResult_lt {P : RP} (σ : State) (j : Nat) (hn : 0 < P.n) :
    (fusedResult P σ j).getD 0 < P.n := by
  unfold fusedResult
  split
  · rename_i hn1
    exact VG.Proof.Rsa.Fused.root_getD_lt hn
      (VG.Proof.Rsa.Fused.bounded_eval hn1)
  · exact hn

def fusedFinish (P : RP) (j : Nat) : FinishInputs P :=
  ⟨fun σ => (fusedResult P σ j).getD 0,
    fun σ => (fusedResult P σ j).isSome,
    fun σ hn => fusedResult_lt σ j hn⟩

/-- This also covers invalid exponents admitted to the candidate search. -/
theorem fusedResult_eq {P : RP} {σ : State} (pre : In P σ) (go : goOn P σ = true)
    (hn : 1 < P.n) (j : Nat) :
    fusedResult P σ j = VG.Spec.Rsa.recoverStep P.n (tv P σ) (rv P σ) (j + 2) := by
  obtain ⟨_, _, positive, even⟩ := mv_facts go
  have fit : mv P σ < 2 ^ P.c := by
    have upper := M_lt pre
    simp only [mv] at *
    omega
  have split := hvs_eq pre go
  simp only [fusedResult, hn, ↓reduceIte, tv, rv, split]
  exact VG.Proof.Rsa.Fused.eval_result P.n (j + 2) (mv P σ) P.c hn positive fit even

end VG.Proof.Rsa.Arm.Recover
