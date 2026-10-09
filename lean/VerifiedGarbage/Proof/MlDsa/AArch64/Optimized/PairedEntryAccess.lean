import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProlog
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernelReady

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure EntryAccess (s : State) : Prop where
  table : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 off) 16
  common : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16
  secret : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16
  workRead : ∀off,off+16≤2176 → InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 off) 16
  workWrite : ∀off,off+16≤2176 → InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 off) 16
  dataRead : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16
  dataWrite : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16

theorem EntryAccess.kernel {s t : State} (h : EntryAccess s) {rs : List Reg}
    (hk : Keep rs s t) (ha : Arguments s t)
    (ht : t.gpr .x1=s.syms "VG_MLDSA_INV_PAIR") : KernelAccess t := by
  constructor
  · simpa only [hk.rd,hk.wr,ht] using h.table
  · simpa only [hk.rd,hk.wr,ha.common] using h.common
  · simpa only [hk.rd,hk.wr,ha.secret] using h.secret
  · simpa only [hk.rd,hk.wr,ha.work] using h.workRead
  · intro off ho
    rw [hk.wr,ha.work]
    exact h.workWrite off (by omega)
  · simpa only [hk.rd,hk.wr,ha.data] using h.dataRead
  · simpa only [hk.wr,ha.data] using h.dataWrite

theorem EntryAccess.save {s : State} (h : EntryAccess s) :
    ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 p.2) 16 := by
  intro p hp
  obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
  exact h.workWrite _ (by omega)

theorem KernelAccess.gamma {s t : State} (h : KernelAccess s)
    (hk : Keep [.x17,.x7] s t) : KernelAccess t := by
  constructor
  · simpa only [hk.rd,hk.wr,hk.get .x1 (by decide)] using h.table
  · simpa only [hk.rd,hk.wr,hk.get .x13 (by decide)] using h.common
  · simpa only [hk.rd,hk.wr,hk.get .x14 (by decide)] using h.secret
  · simpa only [hk.rd,hk.wr,hk.get .x0 (by decide)] using h.workRead
  · simpa only [hk.wr,hk.get .x0 (by decide)] using h.workWrite
  · simpa only [hk.rd,hk.wr,hk.get .x15 (by decide)] using h.dataRead
  · simpa only [hk.wr,hk.get .x15 (by decide)] using h.dataWrite

end VG.Proof.MlDsa.AArch64.Optimized.Paired
