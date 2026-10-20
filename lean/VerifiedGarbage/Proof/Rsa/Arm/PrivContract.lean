module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContractGeometry

import VerifiedGarbage.Proof.Rsa.Arm.PrivContractInput
import VerifiedGarbage.Proof.Rsa.Arm.PrivFn
import VerifiedGarbage.Proof.Rsa.Arm.PrivFnCT

/-! # Checked private RSA implements the shared contract and its permitted leakage -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem private_contract_correct (v : CrtImpl) (s : State) (h : (Spec.Rsa.privateCheckedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa (privCode v) s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.privateCheckedContract abi stackBytes).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := privateFn_ok v s (private_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem private_contract_ct (v : CrtImpl) : ConstantTime isa (Spec.Rsa.privateCheckedContract abi stackBytes).pre
    (Spec.Rsa.privateCheckedContract abi stackBytes).pub (privCode v) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := private_contract_pre s hs
  have it := private_contract_pre t ht
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, a1, a2, _, a4, a5, a6, a7, a8, _, a10, _, a12, _, a14, a15⟩ := hp
  have geometry : privateGeometry s = privateGeometry t := by
    simp only [privateGeometry, sp, p0, p2, p3, a0, a1, a2, a4, a5, a6, a7, a8, a10, a12, a14, a15]
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have both : privateBytes s 0 ++ privateBytes s 1 = privateBytes t 0 ++ privateBytes t 1 := byteEq
  have sameLength : (privateBytes s 0).length = (privateBytes t 0).length := by
    simp only [privateBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (s.gpr .r3).toNat = (t.gpr .r3).toNat
    rw [p3]
  have nb := List.append_inj_left both sameLength
  have eb := List.append_inj_right both sameLength
  rw [← geometry] at it
  exact (privateFn_ct v nb eb s t tr1 tr2 u w ⟨is, it, sp⟩ e1 e2).1
end VG.Proof.Rsa.Arm
