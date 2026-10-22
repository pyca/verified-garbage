module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedSquare
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Save a detected root, clearing the old chain on a set exponent bit. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

def fusedNext (P : RP) (j : Nat) (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : VG.Proof.Rsa.Fused.State :=
  VG.Proof.Rsa.Fused.step P.n (j + 2) (fusedBit V) st

def fusedRootA (P : RP) (j : Nat) (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (fusedSquareA P j st) aRoot ((fusedNext P j V st).root.getD 0 * Rm P % P.n)

section
variable {P : RP} {E : State → Prop} {j : Nat} {st : State → VG.Proof.Rsa.Fused.State}
  {V : State → Nat → Nat}

theorem fusedRoot_vp :
    VP (St P E (fun σ => fusedSquareA P j (st σ)) (mX :: fusedKeep)
      (fun σ => fusedAW P σ) [wM] (fun σ => fusedSquareV P (V σ) (st σ))
      fusedSquareSlots P.w nArr)
      (.seq (sel aU aRoot aZ sBit) (sel aRoot aU mY sLive))
      (St P E (fun σ => fusedRootA P j (V σ) (st σ)) (mX :: fusedKeep)
        (fun σ => fusedAW P σ) [wM] (fun σ => fusedSquareV P (V σ) (st σ))
        fusedSquareSlots P.w nArr) := by
  refine VP.seq (St.psel ⟨_, by taint_decide⟩ (o := aU) (a := aRoot) (b := aZ) (sl := sBit)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_) (by decide)) ?_
  · change fusedSquareV P (V σ) (st σ) sBit ≤ 1
    dsimp [fusedSquareV, fusedHitV, fusedHeadV, fusedV, upd,
      sBit, sTmp, sLive, sOk, sDone, sByte, sE1, sE2]
    exact VG.Proof.Rsa.b2n_le _
  refine (St.psel ⟨_, by taint_decide⟩ (o := aRoot) (a := aU) (b := mY) (sl := sLive)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono ?_
      (fun k hk => ⟨hk, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  · change fusedSquareV P (V σ) (st σ) sLive ≤ 1
    dsimp [fusedSquareV, fusedHitV, upd, sLive, sDone]
    exact VG.Proof.Rsa.b2n_le _
  · intro k hk
    have notU : k ≠ aU := (show ∀ k ∈ mX :: fusedKeep, k ≠ aU from by decide) k hk
    refine ⟨by simp only [List.mem_cons]; right; right; exact List.mem_cons.mp hk, ?_⟩
    by_cases root : k = aRoot
    · subst root
      dsimp only [fusedRootA, upd_self]
      change (if fusedSquareV P (V σ) (st σ) sLive = 0 then
          (if fusedSquareV P (V σ) (st σ) sBit = 0 then
            fusedSquareA P j (st σ) aRoot else fusedSquareA P j (st σ) aZ)
          else fusedSquareA P j (st σ) mY) =
        (fusedNext P j (V σ) (st σ)).root.getD 0 * Rm P % P.n
      rw [fusedNext, ← fused_saved]
      have liveVal : fusedSquareV P (V σ) (st σ) sLive =
          b2n (!(st σ).done && decide ((st σ).value * (st σ).value % P.n = 1) && !fusedBit (V σ)) := rfl
      have bitVal : fusedSquareV P (V σ) (st σ) sBit = b2n (fusedBit (V σ)) := rfl
      have rootVal : fusedSquareA P j (st σ) aRoot = (st σ).root.getD 0 * Rm P % P.n := rfl
      have zeroVal : fusedSquareA P j (st σ) aZ = 0 := rfl
      have yVal : fusedSquareA P j (st σ) mY = (st σ).value * Rm P % P.n := rfl
      rw [liveVal, bitVal, rootVal, zeroVal, yVal, b2n_select, b2n_select]

    · simp only [fusedRootA, upd_ne _ _ root, upd_ne _ _ notU]

end
end VG.Proof.Rsa.Arm.Recover
