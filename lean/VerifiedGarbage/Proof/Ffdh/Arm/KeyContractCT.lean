module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFnCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClassification
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPre

/-! Native key generation satisfies the shared timing policy for arbitrary
secret entropy tapes with the same public domain and disclosed attempt status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem key_contract_ct : ConstantTime isa (Spec.Ffdh.generateKeyContract abi 128).pre
    (Spec.Ffdh.generateKeyContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.GenerateKey.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, inputS⟩ := key_data s hs
  have randLength (a : State) (h : (Spec.Ffdh.generateKeyContract abi 128).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
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
  have inputT := key_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) inputS.outputY inputS.privateLength ?_ rfl
  · have status := (List.cons.inj statusEq).1
    rw [← domEq] at status
    simp only [State.addr] at domainBytes entropyBytes
    simp only [count, domain, entropy, domainBytes, entropyBytes] at status
    have classification := keyScalarClass_same p rb rb2 inputS.size inputT.size status
    exact (keyFn_ct classification s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
