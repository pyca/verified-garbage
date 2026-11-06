module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Proof.MlKem.AArch64

/-- The scalar tail uses a single unaligned word load; masking discards the
extra fourth byte. The input region explicitly grants that byte as well. -/
theorem scalarChunk_ok {s : State}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 4) :
    WP isa (.block scalarChunk) s fun t =>
      Only [.x11,.x2,.x5] s t ∧ t.gpr .x2=s.gpr .x2+3 ∧
      t.gpr .x5=s.gpr .x5-1 ∧
      t.gpr .x11=(s.mem.readW (s.gpr .x2) 32).setWidth 64 &&& s.gpr .x10 := by
  refine wp_ldrw (a := s.gpr .x2) (by decide) (ptr_zero _) hr fun a ha ea =>
    wp_and fun b hb eb => wp_addImm (by decide) fun c hc ec =>
    wp_subImm (by decide) fun t ht et => wp_nil ?_
  refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x2,ec,hb.get .x2,ha.get .x2]; rfl
  · rw [et,hc.get .x5,hb.get .x5,ha.get .x5]; rfl
  · rw [ht.get .x11,hc.get .x11,eb,ea,ha.get .x10]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
