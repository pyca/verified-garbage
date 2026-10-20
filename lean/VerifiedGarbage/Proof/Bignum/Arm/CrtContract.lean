module

import VerifiedGarbage.Proof.Bignum.Arm.CrtContractInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtFnCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Arm.CrtFn

/-! # Private CRT RSA satisfies its shared contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_contract_correct (s : State) (h : (Spec.Rsa.privateCrtContract abi 56).pre s) :
    ∃ tr t, Exec isa CrtFn.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.privateCrtContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := crtFn_ok s (crt_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem crt_contract_ct : ConstantTime isa (Spec.Rsa.privateCrtContract abi 56).pre
    (Spec.Rsa.privateCrtContract abi 56).pub CrtFn.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := crt_contract_pre s hs
  have it := crt_contract_pre t ht
  sig_pub [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, _, a2, a3, a4, a5, a6, _, a8, _, a10, _, a12, a13⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geometry : crtCallGeometry s = crtCallGeometry t := by
    simp only [crtCallGeometry, p0, p2, p3, a0, a2, a3, a4, a5, a6, a8, a10, a12, a13]
  rw [← geometry] at it
  have modulus : crtCallBytes s 0 = crtCallBytes t 0 := byteEq
  exact (crtFn_ct modulus s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm
