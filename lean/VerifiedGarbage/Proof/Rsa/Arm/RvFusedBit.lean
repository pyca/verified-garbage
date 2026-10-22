module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedValue
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedCompare
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3

import VerifiedGarbage.Proof.Framework.Omega

/-! One ARMv7 fused exponentiation and root-search bit, including its trace. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

section
variable {P : RP} {E : State → Prop} {j : Nat} {st : State → VG.Proof.Rsa.Fused.State}
  {V : State → Nat → Nat}

theorem fusedBitFinish_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) :
    VP (St P E (fun σ => fusedValueA P j (V σ) (st σ)) (mX :: fusedKeep)
      (fun σ => AWh P σ P.c) [wR, wM] (fun σ => fusedSquareV P (V σ) (st σ))
      fusedSquareSlots P.w nArr) finishBit
      (FI P E j (fun σ => fusedNext P j (V σ) (st σ))
        (fun σ => upd (V σ) sByte (2 * V σ sByte % 256))) := by
  have pos : 0 < P.n := by omega
  simp only [finishBit, seqs]
  refine VP.seq (St.peqMont hn false (d := sE1) (a := mY)
    (y := fun σ => (fusedNext P j (V σ) (st σ)).value) eqY1_taint
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_)) ?_
  · refine ⟨?_, ?_, VG.Proof.Rsa.Fused.step_lt _ _ _ _ pos⟩ <;>
      simp [fusedValueA, fusedRootA, fusedSquareA, fusedA, AM, upd, mY, aO, aNg, aRoot, mX, mG]
  refine VP.seq (St.peqMont hn true (d := sE2) (a := mY)
    (y := fun σ => (fusedNext P j (V σ) (st σ)).value) eqY2_taint
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_)) ?_
  · refine ⟨?_, ?_, VG.Proof.Rsa.Fused.step_lt _ _ _ _ pos⟩ <;>
      simp [fusedValueA, fusedRootA, fusedSquareA, fusedA, AM, upd, mY, aNg, aRoot, mX, mG]
  refine (St.pfusedTail
    (dn := fun σ => (((st σ).done || decide ((st σ).value * (st σ).value % P.n = 1) ||
      decide ((st σ).value * (st σ).value % P.n = P.n - 1)) && !fusedBit (V σ)))
    (bit := fun σ => fusedBit (V σ))
    (e1 := fun σ => decide ((fusedNext P j (V σ) (st σ)).value = 1))
    (e2 := fun σ => decide ((fusedNext P j (V σ) (st σ)).value = P.n - 1))
    (by decide) (fun σ _ => ?_)).mono (fun _ _ h => h) fun σ s h => h.mono ?_
      (fun k hk => ⟨hk, rfl⟩) ?_
  · dsimp [upd, fusedSquareV, fusedHitV, fusedHeadV, fusedV,
      sBit, sDone, sOk, sLive, sTmp, sByte, sE1, sE2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro k hk
    refine ⟨List.mem_cons_of_mem _ hk, ?_⟩
    simp only [fusedKeep, liveM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp [fusedValueA, fusedRootA, fusedSquareA, fusedA, AM, upd,
      aRoot, mY, mG, mX, aNg, aO, mR2, aOne, aZ, aN]
  · intro d hd
    refine ⟨by simp only [fusedSlots, fusedSquareSlots, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hd ⊢; aesop, ?_⟩
    have flags := VG.Proof.Rsa.Fused.step_flags P.n (j + 2) (fusedBit (V σ)) (st σ)
    simp only [fusedSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · change b2n _ = b2n (fusedNext P j (V σ) (st σ)).done
      exact congrArg b2n flags.1.symm
    · change b2n _ = b2n (fusedNext P j (V σ) (st σ)).root.isSome
      exact congrArg b2n flags.2.symm
    all_goals rfl

theorem fusedBit_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hj : j < 100)
    (byte : ∀ σ, E σ → V σ sByte < 256) (cand : ∀ σ, E σ → V σ sCand = j) :
    VP (FI P E j st V) bit
      (FI P E j (fun σ => fusedNext P j (V σ) (st σ))
        (fun σ => upd (V σ) sByte (2 * V σ sByte % 256))) := by
  simp only [bit, seqs]
  exact VP.seq (fusedSquare_vp hn byte)
    (VP.seq fusedRoot_vp (VP.seq (fusedValue_vp hn hj cand) (fusedBitFinish_vp hn)))

end
end VG.Proof.Rsa.Arm.Recover
