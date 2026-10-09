import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure SegmentChecks (k off n : Nat) where
  setupHint : VG.Taint.Hint VG.AArch64.Taint.T
  storeHint : VG.Taint.Hint VG.AArch64.Taint.T
  setup : (taint.check (Taint.ofRegs [.x19,.x21]) (.block (setup k off n)) setupHint).isSome=true
  store : (taint.check (Taint.ofRegs [.x19])
    (.block [.str .x .x4 .x19 (counts+8*k)]) storeHint).isSome=true

theorem batchFour_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : ∀k<4,SegmentChecks k off n) :
    RelCT isa (fun s t => Rows 4 blocks σ L s ∧ Rows 4 blocks τ L t)
      (Four.batch variant off n)
      (fun s t => Rows 4 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 4 blocks τ (fun k => rowResult σ k off n (L k)) t) := by
  unfold Four.batch
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 0<4) hn hmod variant
    (checks 0 (by decide)).setup (checks 0 (by decide)).store) ?_
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 1<4) hn hmod variant
    (checks 1 (by decide)).setup (checks 1 (by decide)).store) ?_
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 2<4) hn hmod variant
    (checks 2 (by decide)).setup (checks 2 (by decide)).store) ?_
  refine (rowStep_relCT hp hq pub (by decide : 3<4) hn hmod variant
    (checks 3 (by decide)).setup (checks 3 (by decide)).store).mono (fun _ _ h => h) ?_
  intro s t h
  constructor
  · apply h.1.congr
    intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · apply h.2.congr
    intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem batchTwo_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : ∀k<2,SegmentChecks k off n) :
    RelCT isa (fun s t => Rows 2 blocks σ L s ∧ Rows 2 blocks τ L t)
      (Two.batch variant off n)
      (fun s t => Rows 2 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 2 blocks τ (fun k => rowResult σ k off n (L k)) t) := by
  unfold Two.batch
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 0<2) hn hmod variant
    (checks 0 (by decide)).setup (checks 0 (by decide)).store) ?_
  refine (rowStep_relCT hp hq pub (by decide : 1<2) hn hmod variant
    (checks 1 (by decide)).setup (checks 1 (by decide)).store).mono (fun _ _ h => h) ?_
  intro s t h
  constructor
  · apply h.1.congr
    intro k hk
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;> rfl
  · apply h.2.congr
    intro k hk
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
