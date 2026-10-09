import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts signRootConsts_eq)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The optimized key generator uses the same immutable transform tables as
signing. Its ordinary buffer and leakage contract is unchanged. -/
theorem staticRoots_entry {p : Params} {S : Nat} {s : State}
    (hS : 0<S) (h : (keyGenContract p (abi.withConsts signRootConsts) S).pre s) :
    kgPre p S s ∧ StaticRoots S s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  sig_pre [keyGenContract,keyGenSig,abi,argRegs,Abi.withConsts,signRootConsts_eq,
    nttConsts_eq,Inverse.inverseConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hsp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,ht,hw,d1,d2,d3,d4,d5,d6,
    k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  have hrd : s.rd=[⟨s.gpr .x0,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩] := by
    rw [← List.take_append_drop (s.rd.length-2) s.rd,ht,hd]
  refine ⟨⟨?_,by rw [hrd]; simp⟩,⟨⟨hf,hff,?_,hfw,hfs⟩,⟨hi,hif,?_,hiw,his⟩⟩⟩
  · sig_pre [keyGenContract,keyGenSig,abi,argRegs,stackBelow]
    exact ⟨hsp,hw,d1,d2,d3,d4,d5,d6,k1,k2,k3,k4,n1,n2,n3,n4⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]; simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]; simp

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
