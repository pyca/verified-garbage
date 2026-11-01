module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Compose
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval

-- separate module: discharge the source-first scratch signature and its outgoing frame.
/-! # Correctness of the split-seal scratch implementation -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


theorem scratch_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} (hs : scratchContract.pre s) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.seal s
      (fun t => abiPreserved s t ∧ scratchContract.post s t) := by
  have lay := layout_pre s hs
  refine WP.alloc (by decide) lay.spFit.1 ?_
  refine WP.seq (WP.mono (Prelude.ok (allocated 112 s) (prelude_config s hs)) fun u hu => ?_)
  subst u
  refine WP.mono (prepared_ok hs) fun t ht => ?_
  refine ⟨⟨?_,?_,ht.1.2.2⟩,?_⟩
  · intro r hr
    change t.gpr r=s.gpr r
    rw [ht.1.1 r hr]
    exact prepared_gpr s r (by
      have hp : ∀ r ∈ preserved, r∉[Reg.r0,.r9,.r10,.r11,.r12] := by decide
      exact hp r hr)
  · change t.sp+112=s.sp
    rw [ht.1.2.1]
    change s.sp-112#64+112=s.sp
    exact BitVec.sub_add_cancel _ _
  · have hctx : ∀ r ∈ [stackR s,workR s], (contextR s).Disjoint r := by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (lay.stackApart (contextR s) (by simp)).symm
      · exact lay.workApart (contextR s) (by simp)
    have hc : Spec.Gcm.ctxCiph (prepared s).mem (s.gpr .r3) (s.gpr .r4).toNat=
        Spec.Gcm.ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat := ciph_keep (prepared_frame s) hctx lay.rounds
    have hh : Spec.Gcm.ctxH (prepared s).mem (s.gpr .r3)=Spec.Gcm.ctxH s.mem (s.gpr .r3) := ctxH_keep (prepared_frame s) hctx
    have hnonce : Spec.Aes.bytesAt (prepared s).mem (s.gpr .r5) (s.gpr .r6).toNat=
        Spec.Aes.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat := prepared_bytes s hs (nonceR s) (by simp)
    have haad : Spec.Aes.bytesAt (prepared s).mem (s.gpr .r7) (s.gpr .r8).toNat=
        Spec.Aes.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat := prepared_bytes s hs (aadR s) (by simp)
    have hp := ht.2
    simp only [prepared_gpr s .r3 (by decide),prepared_gpr s .r4 (by decide),prepared_gpr s .r5 (by decide),
      prepared_gpr s .r6 (by decide),prepared_gpr s .r7 (by decide),prepared_gpr s .r8 (by decide),
      prepared_destination s hs,prepared_length s hs,prepared_tag s hs,hc,hh,hnonce,haad,plaintext] at hp
    sig_eval [scratchContract,Sig.scratchContract,Sig.withScratch,Curry.withScratch,Curry.app,Spec.Gcm.sealSplitSig,
      Spec.Gcm.sealSplitPost,PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
    intro _ _
    exact hp

end VG.Proof.AesGcm.PPC64LE.SealSplit
