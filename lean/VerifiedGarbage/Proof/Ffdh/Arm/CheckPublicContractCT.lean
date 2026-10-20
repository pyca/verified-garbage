module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFnCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre

/-! The native public check has the timing policy of the shared FFDH signature. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem checkPublic_contract_ct : ConstantTime isa (Spec.Ffdh.checkPublicContract abi 128).pre
    (Spec.Ffdh.checkPublicContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckPublic.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, base, domain, value, count, capacity, domainBytes, valueBytes, inputS⟩ := checkPublic_data s hs
  have lengths (a : State) (h : (Spec.Ffdh.checkPublicContract abi 128).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_pub [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [lengths s hs, lengths t ht, ← p0, ← p1, ← p2, ← p3] at byteEq
  obtain ⟨domEq, yEq⟩ := List.append_inj byteEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have inputT := checkPublic_input t ht (p := p) (yb := yb)
    (p5.symm.trans base) (p0.symm.trans domain) (p3.symm.trans value)
    (by rw [← p2]; exact count) (by rw [← p6]; exact capacity) ?_ ?_
  · exact (checkPublicFn_ct inputS.length s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← value, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← yEq, value, count]
    exact valueBytes

end VG.Proof.Ffdh.Arm
