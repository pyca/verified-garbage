module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeContract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyConsts
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SatWitness
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.AArch64.Target

/-! A concrete valid domain and public constant table witness the initializer ABI. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached

private def precomputeBase : State where
 gpr r:=match r with
  | .x0=>0x100000 | .x1=>275 | .x2=>0x3000 | .x3=>128 | .x4=>64 | .x5=>0x9000 | .x6=>1056 | _=>0
 sp:=0x8000
 mem:=Sat.domainMem
 rd:=[⟨0x3000,128⟩]
 wr:=[⟨0x100000,2200⟩,⟨0x9000,8448⟩]

@[irreducible] private def precomputeMem (W : List (BitVec 64)) : Mem :=fun a=>
 if (a-0x200000).toNat<17744 then constMem 0x200000 W a else Sat.domainMem a

private def precomputeSat (W : List (BitVec 64)) : State :=
 {precomputeBase with mem:=precomputeMem W,rd:=precomputeBase.rd++[⟨0x200000,17744⟩],syms:=fun _=>0x200000}

private theorem precomputeMem_held (W : List (BitVec 64)) (length : W.length=2218) (i : Nat) (hi : i<W.length) :
 (precomputeMem W).readW (0x200000+BitVec.ofNat 64 (8*i)) 64=W.getD i 0 :=by
 rw [←constMem_held 0x200000 W (by rw [length];decide) i hi]
 apply Mem.readW_congr
 intro j hj
 unfold precomputeMem
 refine ite_eq_left ?_
 rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat,Offset.add_sub_cancel_left,BitVec.toNat_ofNat]
 rw [length] at hi
 omega

private theorem precomputeSat_domain (W : List (BitVec 64)) : Spec.Rsa.bytesAt (precomputeMem W) 0x3000 128=Sat.domain :=by
 unfold Sat.domain Spec.Rsa.bytesAt
 apply List.map_congr_left
 intro i hi
 unfold precomputeMem
 apply ite_eq_right
 have small : ∀ i<128,¬((0x3000 : Addr)+BitVec.ofNat 64 i-0x200000).toNat<17744 :=by decide
 exact small i (List.mem_range.mp hi)

private theorem precomputeSat_aux (W : List (BitVec 64)) (length : W.length=2218) :
 ∃s,(Spec.Ffdh.generationPrecomputeContract (abi.withConsts [(Policy.tableSym,W)])).pre s :=by
 refine ⟨precomputeSat W,pre_consts.mpr ⟨?_,?_⟩⟩
 · sig_pre [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.modulusWords,Spec.Rsa.scratchWords,abi,argRegs]
   repeat' apply And.intro
   all_goals first
    | rfl
    | decide +kernel
    | (apply Region.disjoint_of_sep;decide +kernel)
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt (precomputeMem W) 0x3000 128)=true
       rw [precomputeSat_domain W];exact Sat.domain_valid)
 · refine ⟨?_,?_,?_,?_⟩
   · simp only [precomputeSat,precomputeBase,constRegs,Abi.constRegions,List.map_cons,List.map_nil,length]
     rfl
   · intro c hc i hi
     simp only [List.mem_singleton] at hc
     subst c
     exact precomputeMem_held W length i hi
   · intro r hr
     simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
     obtain ⟨c,rfl,rfl⟩:=hr
     rw [length]
     dsimp only [precomputeSat]
     refine ⟨by decide,?_,?_⟩
     · intro q hq
       change q∈([⟨0x100000,2200⟩,⟨0x9000,8448⟩] : List Region) at hq
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
       rcases hq with rfl|rfl
       all_goals apply Region.disjoint_of_sep;decide
     · intro q hq
       simp only [abi,stackBelow,List.not_mem_nil] at hq
   · intro r hr
     simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
     obtain ⟨c,rfl,rfl⟩:=hr
     dsimp only [precomputeSat]
     decide

theorem precompute_shared_sat : ∃s,(Spec.Ffdh.generationPrecomputeContract (abi.withConsts Policy.tableConsts)).pre s :=
 precomputeSat_aux Policy.tableWords Policy.tableWords_length

end VG.Proof.Ffdh.AArch64.Cached
