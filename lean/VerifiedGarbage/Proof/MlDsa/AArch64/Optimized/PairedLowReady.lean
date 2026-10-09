import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPending
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.Round VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowRunRegs : List VReg := stageRunRegs++[.v30]

structure LowReady (g : Nat) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v31) e=8380417#32
  bias : ∀e<4,vword (s.v .v8) e=4194304#32
  c11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127
  c12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g)
  c13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g)
  c14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g)

theorem LowReady.frame {g : Nat} {s t : State} (h : LowReady g s)
    (hf : StepFrame lowRunRegs s t) : LowReady g t := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v11 (by decide)]; exact h.c11
  · rw [hf.vec .v12 (by decide)]; exact h.c12
  · rw [hf.vec .v13 (by decide)]; exact h.c13
  · rw [hf.vec .v14 (by decide)]; exact h.c14

theorem lowConstantsAt_frame {s t : State} (hf : StepFrame lowRunRegs s t) : lowConstantsAt t=lowConstantsAt s := by
  unfold lowConstantsAt
  rw [hf.vec .v15 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem lowClobs_subset (i : LowIndex) : lowPairClobs (lowRaw0 i) (lowRaw1 i)⊆lowRunRegs := by
  rcases i with ⟨p,j⟩
  revert p j
  decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired
