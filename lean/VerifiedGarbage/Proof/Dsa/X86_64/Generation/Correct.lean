module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryPost
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryRun
import VerifiedGarbage.Proof.Framework.Offset

/-! # Native parameter generation satisfies the shared functional contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64

theorem generation_correct (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    (sp : (Impl.Dsa.X86_64.Generation.code H.sha1 H.sha256 Sq.mm M.mm K.run).all
      (fun i => !isa.writesSp i) = true)
    (depth : (Impl.Dsa.X86_64.Generation.code H.sha1 H.sha256 Sq.mm M.mm K.run).x86_64Depth ≤ 472)
    (ctl : ctlOk (Impl.Dsa.X86_64.Generation.code H.sha1 H.sha256 Sq.mm M.mm K.run) = true)
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 472).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.X86_64.Generation.code H.sha1 H.sha256 Sq.mm M.mm K.run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 472).post s t := by
  have h := generationABI_of pre
  obtain ⟨trace, t, he, result, callee, _, _⟩ := entryRun_ok H M Sq K h
  refine ⟨trace, t, he, ⟨callee, ?_, VG.X86_64.Exec.ctl ctl he⟩, entry_shared_post result⟩
  have hf := Exec.stackFrame (SpSafe.of_all sp) he (by omega)
  have hfb := VG.X86_64.Frame.below_mono hf depth (by decide)
  apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.retOut
    · exact h.retScratch
  · simp only [List.mem_singleton] at hr
    subst r
    exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Dsa.X86_64.Generation
