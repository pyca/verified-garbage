module

import VerifiedGarbage.Proof.Ffdh.Arm.PrivateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateFnCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.PrivatePre
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec

/-! Imported private-key checking satisfies the shared timing policy, including its status leakage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem private_contract_ct : ConstantTime isa (Spec.Ffdh.checkPrivateContract abi 128).pre
    (Spec.Ffdh.checkPrivateContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := private_data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.checkPrivateContract abi 128).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6, p7, p8⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p0, ← p1, ← p2, ← p3, ← p5, ← p6] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, statusEq⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := private_input t ht (p := p) (yb := yb) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans domain) (p3.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p2]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    have status := (List.cons.inj statusEq).1
    rw [← domEq, ← peerEq] at status
    simp only [State.addr] at domainBytes peerBytes scalarBytes
    simp only [count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes] at status
    have classification := privateScalarClass_same p (Spec.Rsa.os2ip yb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip xb2) status
    exact (privateFn_ct (by rw [xLength, x2Length]) classification s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm
