import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSpecPre

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_pre_intro {s : State} (h : LowSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64) (fit3 : (s.gpr .x3).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonAux,h.commonWork,h.secretData,h.secretAux,h.secretWork,
    h.dataAux,h.dataWork,h.auxWork,fit0,fit1,fit2,fit3,fit4,h.products,h.data,h.gamma,h.boundLow,h.boundHigh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
