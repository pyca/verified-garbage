module

public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateInput
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEnvironment
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPre
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFn
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre

/-! ### `Ffdh.Arm.KeyGenerateCorrect`, which only this module used -/

section

/-! ### `Ffdh.Arm.KeyCorrect`, which only this module used -/

section

/-! The complete callable key-generation attempt satisfies the shared contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem key_data (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 128).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyFnInput p rb s := by
  have original := pre
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  have domLength : dom.length = (stackArg s 1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 5
    domain := stackArg s 0
    publicValue := s.gpr .r2
    privateValue := s.gpr .r0
    output := s.gpr .r2
    entropy := stackArg s 3
    len := (stackArg s 6).toNat
    k := (stackArg s 2).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((stackArg s 1).toNat = 3 * (stackArg s 2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let rb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 2).toNat
  exact ⟨p, rb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    key_input s original (p := p) (rb := rb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

end VG.Proof.Ffdh.Arm

end

end


/-! The complete callable key-generation attempt satisfies the shared contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerate_data (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyGenerateFnInput p rb s := by
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, old⟩ := key_data s (keyGenerate_pre128 s pre)
  exact ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, keyGenerate_input s pre base privateValue publicValue domain count capacity
      entropy old.outputY old.privateLength domainBytes entropyBytes⟩

end VG.Proof.Ffdh.Arm

end

end


/-! Cached arguments retain the original attempt geometry and add a canonical context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_data (s : State)
    (pre : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
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
