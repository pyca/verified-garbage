module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.DomainFnCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPre

/-! The native parameter checker satisfies the shared timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem domain_contract_ct : ConstantTime isa (Spec.Ffdh.checkDomainContract abi 128).pre
    (Spec.Ffdh.checkDomainContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckDomain.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, base, domain, count, capacity, domainBytes, inputS⟩ := domain_data s hs
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p1] at byteEq
  have inputT := domain_input t ht (p := p) (p3.symm.trans base) (p0.symm.trans domain)
    (by rw [← p2]; exact count) (by rw [← p4]; exact capacity) ?_
  · exact (domainFn_ct s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← byteEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
