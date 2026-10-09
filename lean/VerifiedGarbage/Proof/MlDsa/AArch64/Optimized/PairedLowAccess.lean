import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowEntry

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega)⟩

theorem LowSpecPre.access {s : State} (h : LowSpecPre s) : EntryAccess s := by
  constructor
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

theorem pairedLow_machine {s : State} (h : LowSpecPre s) :
    WP isa (selected .r0) s fun t =>
      ∃a b u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Keep [.x17,.x7] a b ∧ b.mem=a.mem ∧ Prepared b u ∧ LowSetup (Round.arg32 s .x5) b u ∧
        Keep entryRegs s t ∧
        let d := lowPassData (Round.arg32 s .x5) (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  have hta := h.tableSep (⟨s.gpr .x3,2048⟩:Region) (by rw [h.wr]; simp)
  refine selected_low_ok ?_ h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) hta
    (h.auxWork.symm.sub_left (Offset.sub_base _ (by decide))) ?_
  · simpa [or_comm,VG.Spec.MlDsa.gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
