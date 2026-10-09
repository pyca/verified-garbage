import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def firstKernel : Prog isa := .seq (.block init)
  (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11))

theorem firstKernel_ok {s : State}
    (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀i:Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16 ∧
      ∀p:Fin 2,InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*p.val+16*i.val)) 16)
    (hw : ∀u<8,∀p:Fin 2,∀i:Fin 8,InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*p.val+16*i.val)) 16) :
    WP isa firstKernel s fun t =>
      Keep [.x0,.x1,.x9,.x10,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 := by
  unfold firstKernel
  refine WP.seq (WP.mono (init_ok s) fun a ⟨ha,hm,hc,hq⟩ => ?_)
  rw [firstBlock_eq]
  refine WP.mono (firstLoop_ok ?_ ?_ hc hq ?_ ?_ ?_) fun t ⟨hk,hqt,h0,h1,h13,h14,hmem⟩ => ?_
  · simpa only [hm,ha.get .x1 (by decide)] using ht
  · simpa only [ha.get .x1 (by decide),ha.get .x0 (by decide)] using hd
  · simpa only [ha.rd,ha.wr,ha.get .x1 (by decide)] using hrt
  · simpa only [ha.rd,ha.wr,ha.get .x13 (by decide),ha.get .x14 (by decide)] using hr
  · simpa only [ha.wr,ha.get .x0 (by decide)] using hw
  · refine ⟨(ha.trans hk).mono,hqt,?_,?_,?_,?_,?_⟩
    · simpa only [ha.get .x0 (by decide)] using h0
    · simpa only [ha.get .x1 (by decide)] using h1
    · simpa only [ha.get .x13 (by decide)] using h13
    · simpa only [ha.get .x14 (by decide)] using h14
    · simpa only [hm,ha.get .x0 (by decide),ha.get .x13 (by decide),ha.get .x14 (by decide)] using hmem

end VG.Proof.MlDsa.AArch64.Optimized.Paired
