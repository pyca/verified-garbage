module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGenerateFnCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClassification
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
public import VerifiedGarbage.TCB.Arm.Isa
public import Init.Prelude
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.TCB.Artifact

/-! Native key generation satisfies the shared timing policy for arbitrary
secret entropy tapes with the same public domain and disclosed attempt status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts tableSym tableWords)

theorem vettedKeyGenerate_contract_ct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env ScalarLayout.vetted sample) (law : SampleTailLaw tail)
    (makeEnvironment : ∀ (s : State),
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s →
      ∀ {p : Inputs} {rb : List Byte}, KeyGenerateFnInput p rb s → env.holds p (entered s))
    (publicEnvironment : ∀ (s t : State), s.syms tableSym = t.syms tableSym → env.publicRel s t) :
    ConstantTime isa (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pub
      (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, inputS⟩ := vettedKeyGenerate_data_base s hs
  have randLength (a : State) (h : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    have h := (vettedKeyGenerate_pre h).1
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  have symbol := VettedGroups.consts_singleton_symEq (name := tableSym) (words := tableWords) (pub_consts.mp hp).2
  have hp := (pub_consts.mp hp).1
  sig_pub [Spec.Ffdh.vettedGenerateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, p4, p5, p6, p7, _, p9, p10⟩ := hp
  rw [randLength s hs, randLength t ht, ← p4, ← p5, ← p6, ← p7] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let rb2 := Spec.Rsa.bytesAt t.mem (State.addr p.entropy) p.k
  have inputT := vettedKeyGenerate_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) inputS.outputY inputS.privateLength ?_ rfl
  · have status := (List.cons.inj statusEq).1
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
    exact (sampleKeyGenerateFn_ct prepare sample tail env ScalarLayout.vetted prep sampler law
      (fun _ => classification) s t tr1 tr2 u v
      ⟨⟨inputS, makeEnvironment s hs inputS⟩, ⟨inputT, makeEnvironment t ht inputT⟩,
        publicEnvironment s t symbol, sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
