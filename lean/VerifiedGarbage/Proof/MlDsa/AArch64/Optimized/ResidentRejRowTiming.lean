import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem Pub.rowResult {v k off n : Nat} {σ τ : State} (h : Pub v σ τ)
    (hk : k<v) (L : List Zq) : rowResult σ k off n L=rowResult τ k off n L := by
  have hb : streamBytes σ k off (3*n)=streamBytes τ k off (3*n) := by
    unfold streamBytes
    apply List.map_congr_left
    intro i hi
    exact h.byte hk _
  exact congrArg (VG.Proof.MlDsa.Sample.rnFold L) hb

theorem rowStep_relCT {v blocks k off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    {hintSetup hintStore : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x19,.x21]) (.block (setup k off n)) hintSetup).isSome=true)
    (checkStore : (taint.check (Taint.ofRegs [.x19])
      (.block [.str .x .x4 .x19 (counts+8*k)]) hintStore).isSome=true) :
    RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
      (segment variant k off n)
      (fun s t => Rows v blocks σ (updateRow L k (rowResult σ k off n (L k))) s ∧
        Rows v blocks τ (updateRow L k (rowResult σ k off n (L k))) t) := by
  have ct : RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
      (segment variant k off n) (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hb : off+3*n≤1008 := by have:=h.1.blockBound; omega
    have crs : InRegions (s.rd++s.wr) (countAddress s k) 8 := by
      rw [segment_count_eq h.1.env]
      exact in_scr_rd hp h.1.env.wr (by unfold counts; have:=hp.streams; omega)
    have crt : InRegions (t.rd++t.wr) (countAddress t k) 8 := by
      rw [segment_count_eq h.2.env]
      exact in_scr_rd hq h.2.env.wr (by unfold counts; have:=hq.streams; omega)
    have hs19 : s.gpr .x19=t.gpr .x19 := by rw [h.1.env.x19,h.2.env.x19,pub.2.2.1]
    have hs21 : s.gpr .x21=t.gpr .x21 := by rw [h.1.env.x21,h.2.env.x21,pub.2.1]
    have hm : InputEq s t (segmentInput s k off) n := by
      rw [segment_input_eq h.1.env]
      exact rows_input_eq pub h.1 h.2 hk hn
    exact segment_relCT variant k off n (by have:=hp.streams; omega) (by omega) (by omega)
      checkSetup checkStore (h.1.length k hk) hmod
      (h.1.env.sp.trans (pub.2.2.2.1.trans h.2.env.sp.symm)) hs19 hs21
      (segment_layout hp h.1.env hk hb) (segment_layout hq h.2.env hk hb) crs crt
      (by rw [segment_count_eq h.1.env]; exact h.1.counts k hk)
      (by rw [segment_count_eq h.2.env]; exact h.2.counts k hk)
      (by rw [segment_output_eq h.1.env]; exact h.1.stored k hk)
      (by rw [segment_output_eq h.2.env]; exact h.2.stored k hk)
      hm _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  refine (ct.wp (fun s t h => ⟨rowStep_ok hp h.1 hk hn hmod variant,
    rowStep_ok hq h.2 hk hn hmod variant⟩)).mono (fun _ _ h => h) ?_
  intro s t h
  rw [←pub.rowResult hk (off := off) (n := n) (L k)] at h
  exact h.2

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
