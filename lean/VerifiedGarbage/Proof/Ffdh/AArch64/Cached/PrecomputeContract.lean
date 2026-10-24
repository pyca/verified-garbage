module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! The reviewed initializer ABI, with its existing public constant-table convention. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Spec.Ffdh

abbrev precomputeDomain (s : State) : List Byte :=Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

def precomputePlainPre (s : State) : Prop :=
 let ctx : Region:=⟨s.gpr .x0,(s.gpr .x1).toNat*8⟩
 let dom : Region:=⟨s.gpr .x2,(s.gpr .x3).toNat⟩
 let scr : Region:=⟨s.gpr .x5,(s.gpr .x6).toNat*8⟩
 s.rd=[dom] ∧ s.wr=[ctx,scr] ∧ ctx.Disjoint dom ∧ ctx.Disjoint scr ∧ dom.Disjoint scr ∧
 (s.gpr .x0).toNat+(s.gpr .x1).toNat*8≤2^64 ∧ (s.gpr .x2).toNat+(s.gpr .x3).toNat≤2^64 ∧
 (s.gpr .x5).toNat+(s.gpr .x6).toNat*8≤2^64 ∧
 pLenValid (s.gpr .x4).toNat ∧ domainLenValid (s.gpr .x4).toNat (s.gpr .x3).toNat ∧
 (s.gpr .x1).toNat=generationPrecomputedWords (s.gpr .x4).toNat ∧
 Spec.Rsa.scratchWords (s.gpr .x4).toNat≤(s.gpr .x6).toNat ∧
 domainValid (s.gpr .x4).toNat (precomputeDomain s)

def precomputePre (s : State) : Prop :=
 precomputePlainPre (stripConsts Policy.tableConsts s) ∧ ConstsOk Policy.tableConsts 0 s

def precomputePost (s t : State) : Prop :=
 (t.gpr .x0).setWidth 32=1#32 ∧
 generationPrecompute (s.gpr .x4).toNat (precomputeDomain s)=
  some (Spec.Rsa.wordsAt t.mem (s.gpr .x0) (s.gpr .x1).toNat)

def precomputePub (s t : State) : Prop :=
 s.sp=t.sp ∧ (precomputeDomain s).map (·.toNat)=(precomputeDomain t).map (·.toNat) ∧
 s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧ s.gpr .x3=t.gpr .x3 ∧
 s.gpr .x4=t.gpr .x4 ∧ s.gpr .x5=t.gpr .x5 ∧ s.gpr .x6=t.gpr .x6 ∧ s.syms Policy.tableSym=t.syms Policy.tableSym

def precomputeContract : Contract isa where
 pre:=precomputePre
 post:=precomputePost
 pub:=precomputePub

theorem precompute_shared_plain_pre {s : State} (h : (generationPrecomputeContract abi).pre s) : precomputePlainPre s :=by
 sig_pre [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputePlainPre,pLenValid,domainLenValid] at h
 sig_pre [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputePlainPre,pLenValid,domainLenValid] at h
 sig_split h
 sig_reduce [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputePlainPre,pLenValid,domainLenValid]
 sig_and_intros
 sig_close
 all_goals with_reducible assumption

theorem precompute_shared_pre {s : State} (h : (generationPrecomputeContract (abi.withConsts Policy.tableConsts)).pre s) : precomputePre s :=by
 obtain ⟨plain,constants⟩:=pre_consts.mp h
 exact ⟨precompute_shared_plain_pre plain,constants⟩

end VG.Proof.Ffdh.AArch64.Cached
