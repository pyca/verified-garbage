module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFnCT
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateData
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationMemory
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClassification
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre

/-! Cached attempts compare independent entropy tapes under the reviewed public leakage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_contract_ct (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail) :
    ConstantTime isa (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre
      (Spec.Ffdh.cachedGenerateKeyContract abi 176).pub
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, allInputS,cachedS,validS,cachePointer,cacheWords⟩ := cachedKeyGenerate_data s hs
  have inputS := allInputS.input
  have randLength (a : State) (h : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    have h := cachedKeyGenerate_plain_pre a h
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, p4, p5, p6, p7, _, p9, p10, p11, p12⟩ := hp
  rw [randLength s hs, randLength t ht, ← p4, ← p5, ← p6, ← p7] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let rb2 := Spec.Rsa.bytesAt t.mem (State.addr p.entropy) p.k
  have allInputT := cachedKeyGenerate_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) (p11.symm.trans cachePointer) inputS.outputY inputS.privateLength ?_ rfl
  · have inputT := allInputT.input
    have cachedT := (cachedKeyGenerate_environment t ht (p9.symm.trans base)
      (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
      (by rw [←p6]; exact count) (by rw [←p10]; exact capacity)
      (p11.symm.trans cachePointer) (by rw [←p12]; exact cacheWords)
      (by rw [←p5,←domain]; change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat=p.dom; rw [←domEq,domain]; exact domainBytes)).1
    have status := (List.cons.inj statusEq).1
    rw [← domEq] at status
    simp only [State.addr] at domainBytes entropyBytes
    simp only [count, domain, entropy, domainBytes, entropyBytes] at status
    change Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) =
      Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb2) at status
    rw [← ScalarLayout.vetted_value inputS.size, ← ScalarLayout.vetted_value inputT.size] at status
    have classification := keyStatus_validity_same (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb))
      (Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb2)) status
    rw [p.privateValid_native, p.privateValid_native] at classification
    have modValid := VG.Proof.Ffdh.domainValid_mod validS
    rw [p.domainP] at modValid
    exact (cachedKeyGenerateFn_ct prepare sample tail cachedGenerationEnvironment ScalarLayout.vetted
      prep sampler law CachedSample.layoutBound cachedGeneration_publicRel cachedGeneration_afterMem
      modValid classification s t tr1 tr2 u v
      ⟨⟨allInputS,cachedS⟩,⟨allInputT,cachedT⟩,sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes


end VG.Proof.Ffdh.Arm
