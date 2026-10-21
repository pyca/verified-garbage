module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSatWitness
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.Arm.Target

/-! A real canonical public context witnesses the cached native attempt ABI. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def cachedAttemptBase : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a=0x8001 then 0x30 else if a=0x8004 then 0x80 else if a=0x8008 then 0x40
    else if a=0x800d then 0x70 else if a=0x8010 then 0x40 else if a=0x8015 then 0x90
    else if a=0x8018 then 0x20 else if a=0x8019 then 4 else if a=0x801e then 0x10
    else if a=0x8020 then 0x13 else if a=0x8021 then 1 else CachedSat.domainMem a
  rd := [⟨0x3000,128⟩,⟨0x7000,64⟩,⟨0x100000,2200⟩,⟨0x8000,36⟩]
  wr := [⟨0x1000,64⟩,⟨0x2000,64⟩,⟨0x9000,8448⟩]

private def cachedAttemptSat : State :=
  {cachedAttemptBase with mem := CachedSat.withContext cachedAttemptBase.mem}

private theorem cachedAttempt_arg (i : Nat) (hi : i<9) :
    stackArg cachedAttemptSat i=stackArg cachedAttemptBase i := by
  apply CachedSat.readW_outside
  have small : ∀ i<9, (stackArgAddr cachedAttemptBase i).toNat+4≤0x100000 := by decide
  exact small i hi

private theorem cachedAttempt_domain :
    Spec.Rsa.bytesAt cachedAttemptSat.mem 0x3000 128=CachedSat.domain := by
  rw [show cachedAttemptSat.mem=CachedSat.withContext cachedAttemptBase.mem from rfl,CachedSat.domain_unchanged]
  unfold CachedSat.domain
  decide +kernel

theorem cachedKeyGenerate_sat : ∃ s, (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s := by
  refine ⟨cachedAttemptSat,?_⟩
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
    Spec.Ffdh.pLenValid,Spec.Ffdh.domainLenValid,abi,argRegs,reduceClassify,Loc.val,State.addr]
  simp only [cachedAttempt_arg 0 (by decide),cachedAttempt_arg 1 (by decide),cachedAttempt_arg 2 (by decide),
    cachedAttempt_arg 3 (by decide),cachedAttempt_arg 4 (by decide),cachedAttempt_arg 5 (by decide),
    cachedAttempt_arg 6 (by decide),cachedAttempt_arg 7 (by decide),cachedAttempt_arg 8 (by decide)]
  have a0 : stackArg cachedAttemptBase 0=0x3000 := by decide
  have a1 : stackArg cachedAttemptBase 1=128 := by decide
  have a2 : stackArg cachedAttemptBase 2=64 := by decide
  have a3 : stackArg cachedAttemptBase 3=0x7000 := by decide
  have a4 : stackArg cachedAttemptBase 4=64 := by decide
  have a5 : stackArg cachedAttemptBase 5=0x9000 := by decide
  have a6 : stackArg cachedAttemptBase 6=1056 := by decide
  have a7 : stackArg cachedAttemptBase 7=0x100000 := by decide
  have a8 : stackArg cachedAttemptBase 8=275 := by decide
  rw [a0,a1,a2,a3,a4,a5,a6,a7,a8]
  dsimp only [cachedAttemptSat,cachedAttemptBase]
  repeat' apply And.intro
  all_goals first
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt cachedAttemptSat.mem 0x3000 128)=true
       rw [cachedAttempt_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt cachedAttemptSat.mem 0x3000 128) =
         some (Spec.Rsa.wordsAt cachedAttemptSat.mem 0x100000 275)
       rw [cachedAttempt_domain]; exact (CachedSat.canonical _).2)
    | decide +kernel
    | (apply Region.disjoint_of_sep; decide +kernel)

end VG.Proof.Ffdh.Arm
