module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SatWitness
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.AArch64.Target

/-! A canonical context and empty tape witness the complete cached controller ABI. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof
open VG VG.AArch64

private def keyBase : State where
 gpr r:=match r with
  | .x0=>0x1000 | .x1=>64 | .x2=>0x2000 | .x3=>64 | .x4=>0x5000 | .x5=>0x3000 | .x6=>128 | .x7=>64 | _=>0
 sp:=0x6000
 mem a:=if a=0x6001 then 0x70 else if a=0x6011 then 0x80 else if a=0x6018 then 0x20
  else if a=0x6019 then 4 else if a=0x6021 then 0x40 else if a=0x4010 then 0x40
  else if a=0x602a then 0x10 else if a=0x6030 then 0x13 else if a=0x6031 then 1 else Sat.domainMem a
 rd:=[⟨0x3000,128⟩,⟨0x7000,0⟩,⟨0x100000,2200⟩,⟨0x6000,56⟩]
 wr:=[⟨0x1000,64⟩,⟨0x2000,64⟩,⟨0x5000,8⟩,⟨0x8000,8448⟩,⟨0x4000,128⟩]

private def keySat : State :={keyBase with mem:=Sat.withContext keyBase.mem}

private theorem key_arg (i : Nat) (hi : i<7) : stackArg keySat i=stackArg keyBase i :=by
 apply Sat.readW_outside
 have small : ∀i<7,(stackArgAddr keyBase i).toNat+8≤0x100000 :=by decide
 exact small i hi

private theorem key_domain : Spec.Rsa.bytesAt keySat.mem 0x3000 128=Sat.domain :=by
 rw [show keySat.mem=Sat.withContext keyBase.mem from rfl,Sat.domain_unchanged]
 unfold Sat.domain
 decide +kernel

private theorem key_control (i : Nat) (hi : i<3) : keySat.mem.readW (0x4000+BitVec.ofNat 64 (8*i)) 64=
 keyBase.mem.readW (0x4000+BitVec.ofNat 64 (8*i)) 64 :=by
 apply Sat.readW_outside
 have small : ∀i<3,((0x4000 : Addr)+BitVec.ofNat 64 (8*i)).toNat+8≤0x100000 :=by decide
 exact small i hi

theorem key_sat : ∃s,(Spec.Ffdh.cachedKeySearchContract abi 64).pre s :=by
 refine ⟨keySat,?_⟩
 sig_pre [Spec.Ffdh.cachedKeySearchContract,Spec.Ffdh.cachedKeySearchSig,Spec.Ffdh.keySearchSig,
  Spec.Ffdh.pLenValid,Spec.Ffdh.domainLenValid,Spec.Ffdh.generationContextAt,abi,argRegs]
 simp only [key_arg 0 (by decide),key_arg 1 (by decide),key_arg 2 (by decide),key_arg 3 (by decide),key_arg 4 (by decide),key_arg 5 (by decide),key_arg 6 (by decide)]
 have a0 : stackArg keyBase 0=0x7000 :=by decide
 have a1 : stackArg keyBase 1=0 :=by decide
 have a2 : stackArg keyBase 2=0x8000 :=by decide
 have a3 : stackArg keyBase 3=1056 :=by decide
 have a4 : stackArg keyBase 4=0x4000 :=by decide
 have a5 : stackArg keyBase 5=0x100000 :=by decide
 have a6 : stackArg keyBase 6=275 :=by decide
 rw [a0,a1,a2,a3,a4,a5,a6]
 dsimp only [keySat,keyBase]
 repeat' apply And.intro
 all_goals first
  | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128)=true
     rw [key_domain];exact Sat.domain_valid)
  | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128)=some (Spec.Rsa.wordsAt keySat.mem 0x100000 275)
     rw [key_domain];exact (Sat.canonical _).2)
  | (change (keySat.mem.readW 0x4000 64).toNat≤128
     rw [show (0x4000 : Addr)=0x4000+BitVec.ofNat 64 (8*0) from rfl,key_control 0 (by decide)];decide)
  | (change (keySat.mem.readW (0x4000+8) 64).toNat≤128
     rw [show (0x4000+8 : Addr)=0x4000+BitVec.ofNat 64 (8*1) from rfl,key_control 1 (by decide)];decide)
  | (change keySat.mem.readW (0x4000+16) 64=BitVec.ofNat 64 64
     rw [show (0x4000+16 : Addr)=0x4000+BitVec.ofNat 64 (8*2) from rfl,key_control 2 (by decide)];decide)
  | decide +kernel
  | (apply Region.disjoint_of_sep;decide +kernel)

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
