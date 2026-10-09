import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Proof.MlKem.AArch64

/-- Exact store semantics are retained even on rejection. This stronger
frame is needed to reproduce the legacy sampler's final rejected coefficient. -/
theorem accept_memory_ok {s : State}
    (hw : InRegions s.wr (s.gpr .x3) 4) :
    WP isa (.block rnAccept) s fun t =>
      Keep [.x3,.x4,.x13,.x14,.x15] s t ∧
      t.mem=s.mem.writeW (s.gpr .x3) ((s.gpr .x11).setWidth 32) ∧
      t.gpr .x3=s.gpr .x3+(((s.gpr .x11-s.gpr .x9)>>>63)<<<2) ∧
      t.gpr .x4=s.gpr .x4-((s.gpr .x11-s.gpr .x9)>>>63) := by
  refine wp_sub fun a ha ea => wp_lsr (by decide) fun b hb eb =>
    wp_strw (a := s.gpr .x3) (by decide)
      (by rw [hb.get .x3,ha.get .x3]; exact ptr_zero _)
      (by rw [hb.wr,ha.wr]; exact hw) fun c hc =>
    wp_lsl (by decide) fun d hd ed => wp_add fun e he ee =>
    wp_sub fun t ht et => wp_nil ?_
  refine ⟨(((((ha.keep.trans hb.keep).trans hc.keep).trans hd.keep).trans he.keep).trans
      ht.keep).mono (by decide),?_,?_,?_⟩
  · rw [ht.mem,he.mem,hd.mem,hc.mem,hb.get .x11,ha.get .x11,hb.mem,ha.mem]
  · rw [ht.get .x3,ee,hd.get .x3,hc.gpr,hb.get .x3,ha.get .x3,
      ed,hc.gpr,eb,ea]
  · rw [et,he.get .x4,hd.get .x4,hc.gpr,hb.get .x4,ha.get .x4,
      he.get .x14,hd.get .x14,hc.gpr,eb,ea]

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
