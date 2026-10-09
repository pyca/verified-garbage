import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

def rootRegions (s : State) : List Region :=
  [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]

theorem entry {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (h : (verifyContract p (abi.withConsts signRootConsts) S).pre s) :
    vPre p S s ∧ StaticRoots S s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  sig_pre [verifyContract,verifySig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,
    InverseTable.expandedWords_length,stackBelow,List.range,List.range.loop] at h
  obtain ⟨hsp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,ht,hw,d1,d2,d3,
    k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  have hrd : s.rd=vInputs p s++rootRegions s := by
    rw [←List.take_append_drop (s.rd.length-2) s.rd,ht,hd]
    rfl
  refine ⟨⟨?_,fun r hr=>by rw [hrd]; exact List.mem_append_left _ hr⟩,
    ⟨⟨hf,hff,?_,hfw,?_⟩,⟨hi,hif,?_,hiw,?_⟩⟩⟩
  · sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop]
    exact ⟨hsp,rfl,hw,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,by rw [hrd]; simp [rootRegions],Region.contains_self _ _⟩
  · exact hfs
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,by rw [hrd]; simp [rootRegions],Region.contains_self _ _⟩
  · exact his

end VG.Proof.MlDsa.AArch64.Verify.Optimized
