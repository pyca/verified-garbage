module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Correct
import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig

-- separate module: the public gather entry is verified against its unchanged signature.
/-! # Verified gather with a direct-source first piece -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE


theorem sat_pre : ∃ s,contract.pre s := by
  sig_implies_sat [contract,Spec.Gcm.sealGatherContract,Spec.Gcm.sealGatherSig,Spec.Gcm.sealGatherPre,PPC64LE.abi,
    PPC64LE.argRegs,Gather.stackArgs_three,List.append_eq]
    [Gather.gatherSat,stackArg,stackArgAddr,Mem.readW,Mem.read] using Gather.gatherSat


theorem verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.GatherSplit.sealGather contract := by
  refine ⟨?_,?_,sat_pre⟩
  · intro s hs
    obtain ⟨t,z,he,ha,hp⟩ := sealGather_wp seal_framed.1 SealSplit.framed.1 (layout_pre hs)
    exact ⟨t,z,he,ha,Gather.gatherPost_of hp⟩
  · intro s t ts tt s' t' hs ht hp es et
    exact sealGather_ct seal_framed.1 seal_framed.2.1 SealSplit.framed.1 SealSplit.framed.2.1
      s t ts tt s' t' (layout_pre hs) (layout_pre ht) (Gather.gatherPub_of hp) es et

end VG.Proof.AesGcm.PPC64LE.GatherSplit
