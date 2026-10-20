module

import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGeneratePre
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre

/-! The vetted attempt uses the same caller-owned buffers and stack frame,
with the reviewed group table added to readable regions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem vettedKeyGenerate_pre {s : State}
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    (Spec.Ffdh.generateKeyContract abi 176).pre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 176 s :=
  pre_consts.mp pre

theorem vettedKeyGenerate_input (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s)
    {p : Inputs} {rb : List Byte}
    (base : stackArg s 5 = p.base) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (domain : stackArg s 0 = p.domain)
    (count : (stackArg s 2).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (entropy : stackArg s 3 = p.entropy) (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb) :
    KeyGenerateFnInput p rb s :=
  keyGenerate_input_stripConsts (keyGenerate_input (stripConsts tableConsts s)
    (vettedKeyGenerate_pre pre).1 base privateValue publicValue domain count capacity
    entropy outputY privateLength domainBytes entropyBytes)

theorem vettedKeyGenerate_data_base (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyGenerateFnInput p rb s := by
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, input⟩ := keyGenerate_data (stripConsts tableConsts s) (vettedKeyGenerate_pre pre).1
  exact ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, keyGenerate_input_stripConsts input⟩

end VG.Proof.Ffdh.Arm
