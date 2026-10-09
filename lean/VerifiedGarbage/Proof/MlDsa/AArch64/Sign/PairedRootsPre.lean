import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedRoots_pre {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (hk : (signK p S).pre s) (hr : StaticRoots S s) (rp : PairedRoots S s)
    (hrd : s.rd=[⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]) :
    (signContractT p (abi.withConsts pairedSignRootConsts) S).pre s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  dsimp only [signK,scrLen] at hk
  rw [Nat.mul_comm 8 (scratchWords p)] at hk
  obtain ⟨_,hw,d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5,hsp⟩ := hk
  sig_pre [signContractT,signSig,abi,argRegs,Abi.withConsts,pairedSignRootConsts_eq,
    nttConsts_eq,Inverse.inverseConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow]
  refine ⟨hsp,?_,hr.forward.held,hr.inverse.held,rp.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,rp.fit,rp.writable,rp.stack,?_,hw,
    d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩
  · rw [hrd]; rfl
  · rw [hrd]; rfl

end VG.Proof.MlDsa.AArch64.Sign
