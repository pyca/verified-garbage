module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTStages
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval

-- separate module: the public signature supplies the source lengths and outgoing stack arguments.
/-! # Constant time of the split-seal scratch implementation -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE
open CTPrelude


theorem scratch_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    ConstantTime isa scratchContract.pre scratchContract.pub Impl.AesGcm.PPC64LE.SealSplit.seal := by
  refine ct_of fun a b ha hb hp => ?_
  sig_pub [scratchContract,Sig.scratchContract,Sig.withScratch,Curry.withScratch,Curry.app,Spec.Gcm.sealSplitSig,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop] at hp
  obtain ⟨hsp,h3,h4,h5,h6,h7,h8,h9,h10,a0,a1,a2,a3⟩ := hp
  have ib : Initial a b := by
    refine ⟨hb,hsp.symm,fun r hr => ?_,fun i hi => ?_⟩
    · simp only [SealEntry.entryRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> symm <;> with_reducible assumption
    · match i with
      | 0 => exact a0.symm
      | 1 => exact a1.symm
      | 2 => exact a2.symm
      | 3 => exact a3.symm
      | i+4 => omega
  refine ⟨Initial a,⟨ha,rfl,fun _ _ => rfl,fun _ _ => rfl⟩,ib,?_⟩
  refine RelCT.alloc (R := fun _ _ => True) (fun _ _ hp => hp.1.sp.trans hp.2.sp.symm) ?_
  have h : CT (AllocatedI a) (.seq (.block Impl.AesGcm.PPC64LE.SealSplit.prelude)
      (Impl.AesGcm.PPC64LE.sealWith Impl.AesGcm.PPC64LE.SealSplit.body)) := by
    refine CT.seq (J := PreparedI a) (prelude_ct a) ?_ (CTStages.stages_ct ha)
    intro u ⟨s,hs,hu⟩
    subst u
    exact WP.mono (Prelude.ok (allocated 112 s) (prelude_config s hs.pre)) fun t ht => ⟨s,hs,ht⟩
  exact RelCT.mono h (fun _ _ ⟨s,t,hp,hs,ht⟩ => ⟨⟨s,hp.1,hs⟩,⟨t,hp.2,ht⟩⟩) (fun _ _ _ => trivial)

end VG.Proof.AesGcm.PPC64LE.SealSplit
