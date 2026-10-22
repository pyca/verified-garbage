module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedRoot
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedMultiply
import VerifiedGarbage.Proof.Rsa.RecoverFusedMont
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The square-or-product selection updates the fused exponent value. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

def fusedValueA (P : RP) (j : Nat) (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (fusedRootA P j V st) mY ((fusedNext P j V st).value * Rm P % P.n)

theorem fusedValue_select (P : RP) (j : Nat) (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) :
    (if b2n (fusedBit V) = 0 then st.value * st.value % P.n * Rm P % P.n
      else (j + 2) * (st.value * st.value % P.n * Rm P % P.n) % P.n) =
      (fusedNext P j V st).value * Rm P % P.n := by
  rw [b2n_select, fusedNext, VG.Proof.Rsa.Fused.step_value]
  split
  · rw [Nat.mul_comm (j + 2), VG.Proof.Rsa.FusedMont.scale]
  · rfl

section
variable {P : RP} {E : State → Prop} {j : Nat} {st : State → VG.Proof.Rsa.Fused.State}
  {V : State → Nat → Nat}

theorem fusedValue_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hj : j < 100)
    (cand : ∀ σ, E σ → V σ sCand = j) :
    VP (St P E (fun σ => fusedRootA P j (V σ) (st σ)) (mX :: fusedKeep)
      (fun σ => AWh P σ P.c) [wR, wM] (fun σ => fusedSquareV P (V σ) (st σ))
      fusedSquareSlots P.w nArr)
      (.seq multiply (sel mY mX mXm sBit))
      (St P E (fun σ => fusedValueA P j (V σ) (st σ)) (mX :: fusedKeep)
        (fun σ => AWh P σ P.c) [wR, wM] (fun σ => fusedSquareV P (V σ) (st σ))
        fusedSquareSlots P.w nArr) := by
  have pos : 0 < P.n := by omega
  refine VP.seq (St.pfusedMultiply hn hj (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun σ e => ?_) (by decide) (by decide) (by decide)) ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [fusedRootA, fusedSquareA, fusedA, AM, upd, aZ, aRoot, mX, mY, mG, aNg, aO, mR2, aOne]
    · simp [fusedRootA, fusedSquareA, fusedA, AM, upd, aN, aRoot, mX, mY, mG, aNg, aO, mR2, aOne, aZ]
    · change (st σ).value * (st σ).value % P.n * Rm P % P.n < P.n
      exact Nat.mod_lt _ pos
    · simp [fusedRootA, fusedSquareA, fusedA, upd, mG, aRoot, mX, mY]
    · dsimp [fusedSquareV, fusedHitV, fusedHeadV, fusedV, upd,
        sCand, sBit, sDone, sOk, sByte, sE1, sE2, sTmp, sLive]
      exact cand σ e
  refine (St.psel ⟨_, by taint_decide⟩ (o := mY) (a := mX) (b := mXm) (sl := sBit)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono ?_
      (fun k hk => ⟨hk, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  · change fusedSquareV P (V σ) (st σ) sBit ≤ 1
    dsimp [fusedSquareV, fusedHitV, fusedHeadV, fusedV, upd,
      sBit, sTmp, sLive, sOk, sDone, sByte, sE1, sE2]
    exact VG.Proof.Rsa.b2n_le _
  · intro k hk
    have notXm : k ≠ mXm := (show ∀ k ∈ mX :: fusedKeep, k ≠ mXm from by decide) k hk
    refine ⟨?_, ?_⟩
    · rw [show scalarLive (mX :: fusedKeep) = mX :: fusedKeep by decide]
      exact List.mem_cons_of_mem mY (List.mem_cons_of_mem mXm hk)
    by_cases same : k = mY
    · subst same
      dsimp [fusedValueA, upd_self]
      change (if fusedSquareV P (V σ) (st σ) sBit = 0 then fusedRootA P j (V σ) (st σ) mX
        else (j + 2) * fusedRootA P j (V σ) (st σ) mX % P.n) =
          (fusedNext P j (V σ) (st σ)).value * Rm P % P.n
      dsimp [fusedSquareV, fusedHitV, fusedHeadV, fusedV, fusedRootA, fusedSquareA, upd,
        sBit, sTmp, sLive, sOk, sDone, sByte, sE1, sE2, mX, aRoot]
      exact fusedValue_select P j (V σ) (st σ)
    · simp only [fusedValueA, upd_ne _ _ same, upd_ne _ _ notXm]

end
end VG.Proof.Rsa.Arm.Recover
