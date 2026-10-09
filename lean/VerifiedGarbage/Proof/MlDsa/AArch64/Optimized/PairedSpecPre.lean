import VerifiedGarbage.Spec.MlDsa.PairedResponse
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedConsts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedConsts_eq : pairedConsts=[("VG_MLDSA_INV_PAIR",expandedWords)] := rfl

structure ZSpecPre (s : State) : Prop where
  rd : s.rd=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
  wr : s.wr=[⟨s.gpr .x2,2048⟩,⟨s.gpr .x4,2176⟩]
  table : PairedTable.Artifact s.mem (s.syms "VG_MLDSA_INV_PAIR")
  tableSep : ∀r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  commonData : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  commonWork : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  secretData : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  secretWork : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  dataWork : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  products : pairedProductsReduced s.mem (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (s.gpr .x2) j)
  boundLow : 1≤((s.gpr .x6).setWidth 32).toNat
  boundHigh : ((s.gpr .x6).setWidth 32).toNat≤524288

theorem pairedZ_pre {s : State}
    (h : (pairedZContract (abi.withConsts pairedConsts)).pre s) : ZSpecPre s := by
  sig_pre [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hdrop,hheld,_,hsep,htake,hwr,hcd,hcw,hsd,hsw,hdw,_,_,_,_,hprod,hdata,hbl,hbh⟩ := h
  refine ⟨?_,hwr,?_,hsep,hcd,hcw,hsd,hsw,hdw,hprod,hdata,hbl,hbh⟩
  · rw [←List.take_append_drop (s.rd.length-1) s.rd,htake,hdrop]
    rfl
  · intro i hi
    refine (hheld i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
