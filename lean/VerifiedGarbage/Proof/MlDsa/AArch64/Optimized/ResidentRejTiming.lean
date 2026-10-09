import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejInitialTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejCleanupTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- The exact four-stream implementation leaks only public pointers and the
seed bytes already declared by the shared matrix-sampling contract. -/
theorem four_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ) Four.code (fun _ _ => True) := by
  unfold Four.code
  apply RelCT.seq (startFour_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.seq (firstFour_left_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (parseFiveFour_relCT hp hq pub)
  apply RelCT.seq (flagsFour_relCT hp hq pub)
  apply RelCT.seq (adaptiveFour_relCT hp hq pub)
  exact cleanupFinishFour_relCT hp hq pub

/-- The two-stream implementation has the same seed-dependent leakage policy
with its precisely sized two-seed and two-polynomial memory footprint. -/
theorem two_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ) Two.code (fun _ _ => True) := by
  unfold Two.code
  apply RelCT.seq (startTwo_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (firstTwo_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (parseFiveTwo_relCT hp hq pub)
  apply RelCT.seq (flagsTwo_relCT hp hq pub)
  apply RelCT.seq (adaptiveTwo_relCT hp hq pub)
  exact cleanupFinishTwo_relCT hp hq pub

theorem four_ct : ConstantTime isa (Pre 4) (Pub 4) Four.code := by
  intro s t tr ur s' t' hp hq pub es et
  exact (four_relCT hp hq pub _ _ _ _ _ _ ⟨rfl,rfl⟩ es et).1

theorem two_ct : ConstantTime isa (Pre 2) (Pub 2) Two.code := by
  intro s t tr ur s' t' hp hq pub es et
  exact (two_relCT hp hq pub _ _ _ _ _ _ ⟨rfl,rfl⟩ es et).1

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
