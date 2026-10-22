module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedInit
public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedFinish
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedByteLoop
import VerifiedGarbage.Proof.Rsa.Arm.RvCand3
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

import VerifiedGarbage.Proof.Framework.Omega

/-! One complete fused candidate, retaining the exponent for subsequent tries. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

def fusedCandidateV (P : RP) (σ : State) (j : Nat) : Nat → Nat :=
  upd (upd (fun _ => 0) sOk (b2n (fusedResult P σ j).isSome)) sCand (j + 1)

abbrev FCF (P : RP) (E : State → Prop) (j : Nat) : State → State → Prop :=
  St P E (finishA P (fusedFinish P j)) Lq (fun σ => fusedAW P σ) [wM]
    (fun σ => fusedCandidateV P σ j) [sCand, sOk] P.w nArr

section
variable {P : RP} {E : State → Prop} {j : Nat}

theorem fusedCandidate_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (h101 : 101 < P.n) (hj : j < 100)
    (sz : Sizes P) (nowrap : P.B.toNat + P.Z ≤ 2 ^ 32)
    (lengths : P.el + P.dl ≤ 2 * P.K) (positive : 0 < P.el + P.dl)
    (fit : ∀ σ, E σ → mv P σ < 2 ^ P.c) :
    VP (FCS P E j) candidate (fun σ s => FCF P E j σ s ∧
      s.z = !(decide (j + 1 < 100) && !(fusedResult P σ j).isSome)) := by
  simp only [candidate, seqs]
  refine VP.seq (fusedInit_vp hn h101 hj fit)
    (VP.seq (fusedByteLoop_vp hn hj sz nowrap lengths positive) ?_)
  refine VP.seq (St.pcopy ⟨_, by taint_decide⟩ (o := mY) (a := aRoot)
    (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine (St.pcandNext (okb := fun σ => (fusedResult P σ j).isSome) (by decide) (by decide)
    (fun σ _ => ?_)).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ⟨h.mono ?_
      (fun k hk => ⟨hk, rfl⟩) ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change j < 100; exact hj
    · simp [fusedV, fusedEval, fusedResult, hn.2, upd_self]
  · intro k hk
    refine ⟨by simp only [Lq, liveM, fusedKeep, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hk ⊢; aesop, ?_⟩
    simp only [Lq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [finishA, fusedFinish, fusedResult, hn.2, fusedA, fusedEval, AM, upd,
      mY, aRoot, mG, aNg, aO, mR2, aOne, aZ, aN]
  · intro d hd
    refine ⟨by simp only [fusedSlots, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; aesop, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    all_goals simp [fusedCandidateV, fusedV, fusedMeta, fusedResult, hn.2, fusedEval, upd, sCand, sOk, sDone, sBytes, sPtr, sByte]
  · simpa [fusedV, fusedMeta, upd, sCand, sDone, sOk, sBytes, sPtr, sByte] using z

end
end VG.Proof.Rsa.Arm.Recover
