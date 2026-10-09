import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParsePublic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Extraction may overread ignored bytes.  Its trace depends only on the input
and output cursors; candidate equality is re-established from the functional
three-byte extraction theorem before the next loop decision. -/
theorem scalarStep_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x2,.x3]))
    (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr))) :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- Both executions take the same scalar iteration from equal meaningful input,
even when their original output buffers and ignored overread bytes differ. -/
theorem scalarLoopStep_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => ParseInv σ b p n L (d+1) s ∧ ParseInv τ b p n L (d+1) t ∧
        s.gpr .x16=t.gpr .x16 ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5 ∧
        t.gpr .x16=t.gpr .x4*t.gpr .x5) := by
  intro s t tr ur s' t' hp es et
  have he := hp.1.publicRegs hm hsp hp.2
  have ht' := scalarStep_ct s t tr ur s' t' trivial trivial
    ⟨he.1,fun r hr => he.2 r (by
      simp only [VG.AArch64.Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp)⟩ es et
  obtain ⟨_,u,eu,hu⟩ := scalarLoopStep_ok hs hp.1 hd hc
  obtain ⟨_,v,ev,hv⟩ := scalarLoopStep_ok ht hp.2 hd (by rw [← parsed_eq hm (by omega) L]; exact hc)
  obtain ⟨_,rfl⟩ := Exec.det es eu
  obtain ⟨_,rfl⟩ := Exec.det et ev
  have hg := hu.1.publicRegs hm hsp hv.1
  exact ⟨ht',hu.1,hv.1,(by rw [hu.2,hv.2,hg.2 .x4 (by simp),hg.2 .x5 (by simp)]),hu.2,hv.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
