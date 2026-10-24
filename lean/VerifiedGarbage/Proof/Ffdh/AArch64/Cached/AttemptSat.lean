module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SatWitness
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.AArch64.Target

/-! A real canonical public context witnesses satisfiability of the native cached ABI. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

private def attemptBase : State where
 gpr r:=match r with
  | .x0=>0x1000 | .x1=>64 | .x2=>0x2000 | .x3=>64 | .x4=>0x3000 | .x5=>128 | .x6=>64 | .x7=>0x7000 | _=>0
 sp:=0x8000
 mem a:=if a=0x8000 then 0x40 else if a=0x8009 then 0x90 else if a=0x8010 then 0x20 else if a=0x8011 then 4
  else if a=0x801a then 0x10 else if a=0x8020 then 0x13 else if a=0x8021 then 1 else Sat.domainMem a
 rd:=[⟨0x3000,128⟩,⟨0x7000,64⟩,⟨0x100000,2200⟩,⟨0x8000,40⟩]
 wr:=[⟨0x1000,64⟩,⟨0x2000,64⟩,⟨0x9000,8448⟩]

private def attemptSat : State :={attemptBase with mem:=Sat.withContext attemptBase.mem}

private theorem attempt_arg (i : Nat) (hi : i<5) : stackArg attemptSat i=stackArg attemptBase i :=by
 apply Sat.readW_outside
 have small : ∀ i<5,(stackArgAddr attemptBase i).toNat+8≤0x100000 :=by decide
 exact small i hi

private theorem attempt_domain : Spec.Rsa.bytesAt attemptSat.mem 0x3000 128=Sat.domain :=by
 rw [show attemptSat.mem=Sat.withContext attemptBase.mem from rfl,Sat.domain_unchanged]
 unfold Sat.domain
 decide +kernel

theorem attempt_shared_sat : ∃ s,(Spec.Ffdh.cachedGenerateKeyContract abi).pre s :=by
 refine ⟨attemptSat,?_⟩
 sig_pre [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
  Spec.Ffdh.pLenValid,Spec.Ffdh.domainLenValid,abi,argRegs]
 simp only [attempt_arg 0 (by decide),attempt_arg 1 (by decide),attempt_arg 2 (by decide),attempt_arg 3 (by decide),attempt_arg 4 (by decide)]
 have a0 : stackArg attemptBase 0=64 :=by decide
 have a1 : stackArg attemptBase 1=0x9000 :=by decide
 have a2 : stackArg attemptBase 2=1056 :=by decide
 have a3 : stackArg attemptBase 3=0x100000 :=by decide
 have a4 : stackArg attemptBase 4=275 :=by decide
 rw [a0,a1,a2,a3,a4]
 dsimp only [attemptSat,attemptBase]
 repeat' apply And.intro
 all_goals first
  | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt attemptSat.mem 0x3000 128)=true
     rw [attempt_domain];exact Sat.domain_valid)
  | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt attemptSat.mem 0x3000 128)=some (Spec.Rsa.wordsAt attemptSat.mem 0x100000 275)
     rw [attempt_domain];exact (Sat.canonical _).2)
  | decide +kernel
  | (apply Region.disjoint_of_sep;decide +kernel)

end VG.Proof.Ffdh.AArch64.Cached
