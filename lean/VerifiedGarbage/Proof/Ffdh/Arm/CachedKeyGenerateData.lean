module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateInput
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEnvironment
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre

/-! Cached arguments retain the original attempt geometry and add a canonical context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_data (s : State)
    (pre : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5=p.base ∧ s.gpr .r0=p.privateValue ∧
      s.gpr .r2=p.publicValue ∧ stackArg s 0=p.domain ∧ (stackArg s 2).toNat=p.k ∧
      (stackArg s 6).toNat=p.len ∧ stackArg s 3=p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k=rb ∧
      CachedKeyGenerateFnInput p rb s ∧ CachedGenerationContext p (entered s) ∧
      Spec.Ffdh.domainValid p.k p.dom=true ∧ stackArg s 7=p.cachedContext ∧
      (stackArg s 8).toNat=p.cachedWords := by
  have plain := cachedKeyGenerate_plain_pre s pre
  obtain ⟨old,rb,base,privateValue,publicValue,domain,count,capacity,entropy,domainBytes,entropyBytes,h⟩ :=
    keyGenerate_data (cachedPlainState s) plain
  let p : Inputs := {old with cachedContext:=stackArg s 7,cachedWords:=(stackArg s 8).toNat}
  have input : CachedKeyGenerateFnInput p rb s := cachedKeyGenerate_input s pre base privateValue publicValue
    domain count capacity entropy rfl h.outputY h.privateLength domainBytes entropyBytes
  have environment := cachedKeyGenerate_environment s pre (p:=p)
    base privateValue publicValue domain count capacity rfl rfl domainBytes
  exact ⟨p,rb,base,privateValue,publicValue,domain,count,capacity,entropy,domainBytes,entropyBytes,
    input,environment.1,environment.2,rfl,rfl⟩

end VG.Proof.Ffdh.Arm
