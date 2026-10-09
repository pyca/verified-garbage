import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernelSplit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Buffer permissions at the internal kernel boundary, after argument remapping. -/
structure KernelAccess (s : State) : Prop where
  table : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16
  common : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16
  secret : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16
  workRead : ∀off,off+16≤2176 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16
  workWrite : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16
  dataRead : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16
  dataWrite : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16

structure Prepared (s u : State) : Prop where
  mem : u.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8
  work : u.gpr .x2=s.gpr .x0
  data : u.gpr .x15=s.gpr .x15
  aux : u.gpr .x16=s.gpr .x16

/-- Exact first-pass setup for either final checker. -/
theorem firstKernel_access_ok {s : State} (ha : KernelAccess s)
    (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩) :
    WP isa firstKernel s fun t =>
      VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x9,.x10,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 :=
  firstKernel_ok ht hd ha.table
    (by
      intro u hu i
      constructor
      · rw [BitVec.add_assoc,←BitVec.ofNat_add]
        exact ha.common _ (by omega)
      · intro p
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        exact ha.secret _ (by omega))
    (by
      intro u hu p i
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact ha.workWrite _ (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.Paired
