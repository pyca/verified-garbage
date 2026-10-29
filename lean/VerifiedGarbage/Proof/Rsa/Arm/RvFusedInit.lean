module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedByte
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedByteInit
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedConstant
import VerifiedGarbage.Proof.Rsa.Arm.RvSt2
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import Aesop

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Arm.RvCand1
import Aesop

/-! Initialize one fused candidate from the shared Montgomery setup. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused

abbrev FCS (P : RP) (E : State → Prop) (j : Nat) : State → State → Prop :=
  St P E (fun _ => AM P) liveM (fun σ => fusedAW P σ) [wM]
    (fun _ => upd (fun _ => 0) sCand j) [sCand] P.w nArr

section
variable {P : RP} {E : State → Prop} {j : Nat}

theorem fusedInit_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (h101 : 101 < P.n) (hj : j < 100)
    (fit : ∀ σ, E σ → mv P σ < 2 ^ P.c) :
    VP (FCS P E j) init (FWI P E j (P.el + P.dl)) := by
  have pos : 0 < P.n := by omega
  have initial (σ : State) (e : E σ) :
      fusedEval P j (P.el + P.dl) σ = VG.Proof.Rsa.Fused.start P.n 1 := by
    unfold fusedEval
    rw [show 8 * (P.el + P.dl) = P.c by simp only [RP.c]; omega,
      Nat.div_eq_of_lt (fit σ e), VG.Proof.Rsa.Fused.eval_zero]
  simp only [init, seqs]
  refine VP.seq (St.pcopy gZ_taint (o := mG) (a := aZ)
    (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pstoreG (by decide) (by decide) (fun σ _ => ⟨?_, ?_⟩) (by decide)) ?_
  · simp only [upd_self]; omega
  · simp [AM, upd, mG, aZ, aOne, mR2, aO, aNg]
  refine VP.seq (St.pmmul (o := iG) (a := iG) (b := iR2) (by decide) hn.1
    (T := fun _ => gR P j 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_)) ?_
  · have g : upd (upd (AM P) mG (AM P aZ)) mG (upd (fun _ => 0) sCand j sCand + 2)
        (mBase + iG) = j + 2 := by simp [upd, mG, mBase, iG]
    have r : upd (upd (AM P) mG (AM P aZ)) mG (upd (fun _ => 0) sCand j sCand + 2)
        (mBase + iR2) = R2v P := by simp [upd, AM, mG, mBase, iR2, mR2, aO, aNg]
    rw [g, r]
    exact ⟨by omega, Nat.mod_lt _ pos, Nat.mod_lt _ pos, gR1_mont j⟩
  refine VP.seq (St.pcopy yO_taint (o := mY) (a := aO)
    (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pcopy ⟨_, by taint_decide⟩ (o := aRoot) (a := aZ)
    (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  simp only [initFlags, List.append_assoc]
  refine VP.seq
    (VP.block_append (St.pconstant (d := sDone) (v := 1) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩)
      (VP.block_append (St.pconstant (d := sOk) (v := 0) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩)
        (St.pconstant (d := sByte) (v := 0) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩))) ?_
  refine St.pfusedByteInit.mono (fun _ _ h => h) fun σ s h => h.mono
    (A' := fun σ => fusedA P j (fusedEval P j (P.el + P.dl) σ)) (L' := fusedKeep)
    (AW' := fun σ => fusedAW P σ) (LW' := [wM])
    (V' := fun σ => fusedV (fusedMeta P j (P.el + P.dl)) (fusedEval P j (P.el + P.dl) σ))
    (LS' := fusedSlots) ?_ (fun k hk => ⟨hk, rfl⟩) ?_
  · intro k hk
    refine ⟨by simp only [fusedKeep, liveM, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hk ⊢; aesop, ?_⟩
    rw [initial σ h.1]
    simp only [fusedKeep, liveM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp [fusedA, VG.Proof.Rsa.Fused.start, AM, upd, gR,
      aRoot, mY, mG, mBase, iG, aNg, aO, mR2, aOne, aZ, aN, Ov]
  · intro d hd
    refine ⟨by simp only [fusedSlots, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; aesop, ?_⟩
    rw [initial σ h.1]
    simp only [fusedSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [byteInitV, fusedV, fusedMeta, VG.Proof.Rsa.Fused.start, upd,
      sDone, sOk, sByte, sCand, sPtr, sBytes, VG.Proof.Rsa.b2n]

end
end VG.Proof.Rsa.Arm.Recover
