import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailHead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok)

/-- Masking makes the legacy cleanup decision depend on exactly the final
three candidate bytes, independently of the fourth byte read by LDR. -/
theorem tailRead_value {s : State} {k : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailRead k)) s fun t => Only [.x6,.x7] s t ∧
      (t.gpr .x6).toNat=candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) ∧
      (t.gpr .x7).toNat=8380417 := by
  unfold tailRead
  simp only [List.cons_append,List.nil_append]
  refine wp_addImm (by omega) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_ldrw (a := s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) (by decide)
      (by rw [ptr_zero,eb,ea,Offset.add_add])
      (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hr) fun c hc ec =>
    wp_movz fun d hd ed => wp_movk1 fun e he ee =>
    wp_and fun f hf ef => movQ_ok fun t ht et => wp_nil ?_
  refine ⟨((((((ha.trans hb).trans hc).trans hd).trans he).trans hf).trans ht).mono (by decide),?_,et⟩
  have h7 : e.gpr .x7=0x7fffff := by rw [ee,ed]; rfl
  rw [ht.get .x6,ef,h7,he.get .x6,hd.get .x6,ec,hb.mem,ha.mem]
  exact scalar_candidate _ _

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
