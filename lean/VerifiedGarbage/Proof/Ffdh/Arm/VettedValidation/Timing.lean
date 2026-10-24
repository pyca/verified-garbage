module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Input
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.FnTiming
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPre
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! Parameter imports reveal only the already-public domain and table addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem constantTime : ConstantTime isa contract.pre contract.pub
    VG.Impl.Ffdh.Arm.VettedValidation.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, base, domain, count, capacity, domainBytes, inputS⟩ := data s hs
  have relation : (Spec.Ffdh.checkDomainContract abi 128).pub s t ∧
      ∀ c ∈ tableConsts, symAddr s c.1 = symAddr t c.1 := pub_consts.mp hp
  have symbols := VettedGroups.consts_singleton_symEq relation.2
  have pubBase := relation.1
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] at pubBase
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4⟩ := pubBase
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p1] at byteEq
  have preT : (Spec.Ffdh.checkDomainContract abi 128).pre (stripConsts tableConsts t) ∧
      ConstsOk tableConsts 128 t := pre_consts.mp ht
  have inputT := domain_input (stripConsts tableConsts t) preT.1 (p := p)
    (p3.symm.trans base) (p0.symm.trans domain)
    (by change (t.gpr .r2).toNat = p.k; rw [← p2]; exact count)
    (by change (stackArg t 0).toNat = p.len; rw [← p4]; exact capacity) ?_
  · have wide := input_widen inputT
    have table := table_input preT.2 wide
    exact (fn_ct s t tr1 tr2 u v ⟨inputS, ⟨wide, table.1, table.2⟩, sp, symbols⟩ e1 e2).1
  · change Spec.Rsa.bytesAt t.mem (State.addr p.domain) (t.gpr .r1).toNat = p.dom
    rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← byteEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm.VettedValidation
