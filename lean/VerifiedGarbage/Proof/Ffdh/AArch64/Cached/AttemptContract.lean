module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! The reviewed cached-attempt contract in native register and stack coordinates. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt i2osp powMod)

abbrev attemptDomain (s : State) : List Byte :=bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
abbrev attemptRandom (s : State) : List Byte :=bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
abbrev attemptParameters (s : State) : Spec.Ffdh.Parameters :=domainOf (s.gpr .x6).toNat (attemptDomain s)
abbrev attemptScalar (s : State) : Nat :=vettedScalarOfOctets (attemptParameters s) (attemptRandom s)

def attemptPre (s : State) : Prop :=
 let xr : Region:=⟨s.gpr .x0,(s.gpr .x1).toNat⟩
 let yr : Region:=⟨s.gpr .x2,(s.gpr .x3).toNat⟩
 let dom : Region:=⟨s.gpr .x4,(s.gpr .x5).toNat⟩
 let rnd : Region:=⟨s.gpr .x7,(stackArg s 0).toNat⟩
 let scr : Region:=⟨stackArg s 1,(stackArg s 2).toNat*8⟩
 let ctx : Region:=⟨stackArg s 3,(stackArg s 4).toNat*8⟩
 let args : Region:=⟨stackArgAddr s 0,40⟩
 s.sp.toNat+40≤2^64 ∧ s.rd=[dom,rnd,ctx,args] ∧ s.wr=[xr,yr,scr] ∧
 xr.Disjoint yr ∧ xr.Disjoint dom ∧ xr.Disjoint rnd ∧ xr.Disjoint scr ∧ xr.Disjoint ctx ∧ xr.Disjoint args ∧
 yr.Disjoint dom ∧ yr.Disjoint rnd ∧ yr.Disjoint scr ∧ yr.Disjoint ctx ∧ yr.Disjoint args ∧
 dom.Disjoint scr ∧ rnd.Disjoint scr ∧ scr.Disjoint ctx ∧ scr.Disjoint args ∧
 (s.gpr .x0).toNat+(s.gpr .x1).toNat≤2^64 ∧ (s.gpr .x2).toNat+(s.gpr .x3).toNat≤2^64 ∧
 (s.gpr .x4).toNat+(s.gpr .x5).toNat≤2^64 ∧ (s.gpr .x7).toNat+(stackArg s 0).toNat≤2^64 ∧
 (stackArg s 1).toNat+(stackArg s 2).toNat*8≤2^64 ∧ (stackArg s 3).toNat+(stackArg s 4).toNat*8≤2^64 ∧
 pLenValid (s.gpr .x6).toNat ∧ domainLenValid (s.gpr .x6).toNat (s.gpr .x5).toNat ∧
 (s.gpr .x1).toNat=(s.gpr .x6).toNat ∧ (s.gpr .x3).toNat=(s.gpr .x6).toNat ∧
 (stackArg s 0).toNat=(s.gpr .x6).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x6).toNat≤(stackArg s 2).toNat ∧
 domainValid (s.gpr .x6).toNat (attemptDomain s) ∧
 generationContextAt s.mem (stackArg s 3) (stackArg s 4).toNat (s.gpr .x6).toNat (attemptDomain s)

def attemptPost (s t : State) : Prop :=
 ((t.gpr .x0).setWidth 32).toNat=keyStatus (attemptParameters s) (attemptScalar s) ∧
 if keyStatus (attemptParameters s) (attemptScalar s)=1 then
  bytesAt t.mem (s.gpr .x0) (s.gpr .x6).toNat=i2osp (attemptScalar s) (s.gpr .x6).toNat ∧
  bytesAt t.mem (s.gpr .x2) (s.gpr .x6).toNat=i2osp (powMod (attemptParameters s).g (attemptScalar s) (attemptParameters s).p) (s.gpr .x6).toNat
 else bytesAt t.mem (s.gpr .x0) (s.gpr .x6).toNat=List.replicate (s.gpr .x6).toNat 0 ∧
  bytesAt t.mem (s.gpr .x2) (s.gpr .x6).toNat=List.replicate (s.gpr .x6).toNat 0

def attemptLeak (s : State) : List Nat :=
 (attemptDomain s).map (·.toNat)++[keyStatus (attemptParameters s) (attemptScalar s)]

def attemptPub (s t : State) : Prop :=
 (∀ r∈argRegs,s.gpr r=t.gpr r) ∧ s.sp=t.sp ∧
 (List.range 5).map (stackArg s)=(List.range 5).map (stackArg t) ∧ attemptLeak s=attemptLeak t

def attemptContract : Contract isa where
 pre:=attemptPre
 post:=attemptPost
 pub:=attemptPub

theorem stackArgs_five (s : State) :
 (List.range 5).map (stackArg s)=[stackArg s 0,stackArg s 1,stackArg s 2,stackArg s 3,stackArg s 4] :=rfl

theorem attempt_shared_pre {s : State} (h : (cachedGenerateKeyContract abi).pre s) : attemptPre s :=by
 sig_pre [cachedGenerateKeyContract,cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptPre,stackArgs_five,List.append_eq,
  pLenValid,domainLenValid] at h
 sig_pre [cachedGenerateKeyContract,cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptPre,stackArgs_five,List.append_eq,
  pLenValid,domainLenValid] at h
 sig_split h
 sig_reduce [cachedGenerateKeyContract,cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptPre,stackArgs_five,
  List.append_eq,pLenValid,domainLenValid]
 sig_and_intros
 sig_close
 all_goals first | with_reducible assumption | exact ⟨by assumption,by assumption⟩

end VG.Proof.Ffdh.AArch64.Cached
