import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttVerified

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

/-- The ordinary signer contract gains only its three immutable artifact tables. -/
def pairedSignRootConsts := VG.Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts ++
  VG.Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts ++ VG.Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts

theorem pairedSignRootConsts_eq : pairedSignRootConsts=[
    ("VG_MLDSA_NTT_EXPANDED",VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords),
    ("VG_MLDSA_INV_FOLDED",VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords),
    ("VG_MLDSA_INV_PAIR",VG.Impl.MlDsa.AArch64.Optimized.Paired.expandedWords)] := rfl

theorem pairedRoots_entry {p : Params} {S : Nat} {s : State}
    (hS : 0<S) (h : (signContractT p (abi.withConsts pairedSignRootConsts) S).pre s) :
    (signK p S).pre s ∧ StaticRoots S s ∧ PairedRoots S s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  sig_pre [signContractT,signSig,abi,argRegs,Abi.withConsts,pairedSignRootConsts_eq,
    nttConsts_eq,
    Inverse.inverseConsts_eq,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hsp,hd,hf,hi,hpair,hff,hfw,hfs,hif,hiw,his,hpf,hpw,hps,ht,hw,d1,d2,d3,d4,d5,d6,d7,
    k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩ := h
  have hrd : s.rd=[⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩] := by
    rw [← List.take_append_drop (s.rd.length-3) s.rd,ht,hd]
  refine ⟨?_,⟨⟨hf,hff,?_,hfw,hfs⟩,⟨hi,hif,?_,hiw,his⟩⟩,⟨?_,hpf,?_,hpw,hps⟩⟩
  · have hsub : [⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩]⊆s.rd := by
      rw [hrd]
      exact List.subset_append_left _ _
    dsimp only [signK,scrLen]
    rw [Nat.mul_comm 8 (scratchWords p)]
    exact ⟨hsub,hw,d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5,hsp⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]
    simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]
    simp

  · exact hpair
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩,?_,Region.contains_self _ _⟩
    rw [hrd]
    simp

end VG.Proof.MlDsa.AArch64.Sign
