module

-- separate module: Decode the generated public signature once for the frame and payload bounds.

public import VerifiedGarbage.Spec.Gcm.Contiguous
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Decode the contiguous POWER ABI once for both source layouts -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Spec.Gcm

abbrev contract := sealContiguousContract VG.PPC64LE.abi 1552

abbrev ctxR (s : State) : Region := ⟨s.gpr .r3,256⟩
abbrev nonceR (s : State) : Region := ⟨s.gpr .r5,(s.gpr .r6).toNat⟩
abbrev aadR (s : State) : Region := ⟨s.gpr .r7,(s.gpr .r8).toNat⟩
abbrev srcR (s : State) : Region := ⟨s.gpr .r9,(stackArg s 0).toNat⟩
abbrev dstR (s : State) : Region := ⟨s.gpr .r10,(stackArg s 0).toNat⟩
abbrev tagR (s : State) : Region := ⟨stackArg s 1,16⟩
abbrev slotsR (s : State) : Region := ⟨stackArgAddr s 0,16⟩
abbrev argsRegions (s : State) : List Region := [ctxR s,nonceR s,aadR s,srcR s,dstR s,tagR s,slotsR s]

structure CallLayout (s : State) : Prop where
  rd : s.rd=[ctxR s,nonceR s,aadR s]++(if s.gpr .r9=s.gpr .r10 then [] else [srcR s])++[slotsR s]
  wr : s.wr=[dstR s,tagR s]
  stack : ∀ r∈argsRegions s,(below s.sp 1552).Disjoint r
  fit : ∀ r∈argsRegions s,r.base.toNat+r.len≤2^64
  dt : (dstR s).Disjoint (tagR s)
  cd : (ctxR s).Disjoint (dstR s)
  alias : s.gpr .r9=s.gpr .r10 ∨ (srcR s).Disjoint (dstR s)
  rounds : (s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14
  space : 1552≤s.sp.toNat

private theorem slots_fit {s : State} (space : s.sp.toNat ≤ 18446744073709551504) :
    (slotsR s).base.toNat+(slotsR s).len≤2^64 := by
  change (s.sp+BitVec.ofNat 64 96).toNat+16≤2^64
  rw [BitVec.toNat_add];simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem layout_of_pre {s : State} (h : contract.pre s) : CallLayout s := by
  sig_pre [contract,sealContiguousContract,sealContiguousSig,Spec.Gcm.sealPre,
    VG.PPC64LE.abi,VG.PPC64LE.argRegs,List.getD,List.range,List.range.loop] at h
  by_cases eq : s.gpr .r9=s.gpr .r10
  · simp [eq,Sig.pairFacts,Sig.conj,List.filterMap_cons,List.filterMap_nil,and_assoc] at h
    obtain ⟨sp,stackEnd,rd,wr,cd,_,_,_,_,_,dt,_,_,bc,bn,ba,bd,bt,br,fc,fn,fa,fd,ft,nr⟩ := h
    refine ⟨by simpa [eq] using rd,wr,?_ ,?_,dt,cd,.inl eq,nr,sp⟩
    · simp only [argsRegions,List.forall_mem_cons]
      exact ⟨bc,bn,ba,by simpa only [srcR,eq] using bd,bd,bt,br,List.forall_mem_nil _⟩
    · simp only [argsRegions,List.forall_mem_cons]
      refine ⟨?_,fn,fa,?_,fd,?_,slots_fit stackEnd,List.forall_mem_nil _⟩
      · change (s.gpr .r3).toNat+256≤2^64;omega
      · change (s.gpr .r9).toNat+_≤_;rwa [eq]
      · change (stackArg s 1).toNat+16≤2^64;omega
  · simp [eq,Sig.pairFacts,Sig.conj,List.filterMap_cons,List.filterMap_nil,and_assoc] at h
    obtain ⟨sp,stackEnd,rd,wr,cd,_,_,_,_,_,sd,_,dt,_,_,bc,bn,ba,bs,bd,bt,br,fc,fn,fa,fs,fd,ft,nr⟩ := h
    refine ⟨by simpa [eq] using rd,wr,?_,?_,dt,cd,.inr sd,nr,sp⟩
    · simp only [argsRegions,List.forall_mem_cons]
      exact ⟨bc,bn,ba,bs,bd,bt,br,List.forall_mem_nil _⟩
    · simp only [argsRegions,List.forall_mem_cons]
      refine ⟨?_,fn,fa,fs,fd,?_,slots_fit stackEnd,List.forall_mem_nil _⟩
      · change (s.gpr .r3).toNat+256≤2^64;omega
      · change (stackArg s 1).toNat+16≤2^64;omega

end VG.Proof.AesGcm.PPC64LE.Contiguous
