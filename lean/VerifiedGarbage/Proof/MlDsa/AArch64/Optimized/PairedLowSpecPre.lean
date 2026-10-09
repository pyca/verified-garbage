import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecPre

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowSpecPre (s : State) : Prop where
  rd : s.rd=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
  wr : s.wr=[⟨s.gpr .x2,2048⟩,⟨s.gpr .x3,2048⟩,⟨s.gpr .x4,2176⟩]
  table : PairedTable.Artifact s.mem (s.syms "VG_MLDSA_INV_PAIR")
  tableSep : ∀r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  commonData : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  commonAux : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  commonWork : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  secretData : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  secretAux : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  secretWork : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  dataAux : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  dataWork : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  auxWork : (⟨s.gpr .x3,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  products : pairedProductsReduced s.mem (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (s.gpr .x2) j)
  gamma : ((s.gpr .x5).setWidth 32).toNat∈gamma2s
  boundLow : 1≤((s.gpr .x6).setWidth 32).toNat
  boundHigh : ((s.gpr .x6).setWidth 32).toNat≤524288

theorem pairedLow_pre {s : State}
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pre s) : LowSpecPre s := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hdrop,hheld,_,hsep,htake,hwr,hcd,hca,hcw,hsd,hsa,hsw,hda,hdw,haw,_,_,_,_,_,hprod,hdata,hgamma,hbl,hbh⟩ := h
  refine ⟨?_,hwr,?_,hsep,hcd,hca,hcw,hsd,hsa,hsw,hda,hdw,haw,hprod,hdata,hgamma,hbl,hbh⟩
  · rw [←List.take_append_drop (s.rd.length-1) s.rd,htake,hdrop]
    rfl
  · intro i hi
    refine (hheld i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
