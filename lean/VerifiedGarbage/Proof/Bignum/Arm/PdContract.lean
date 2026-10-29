module
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Bignum.Arm.PdContractInput
import VerifiedGarbage.Proof.Bignum.Arm.PdWritten
import VerifiedGarbage.Proof.Bignum.Arm.PdFnCT
import VerifiedGarbage.Proof.Bignum.Arm.PdFn
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
import VerifiedGarbage.Proof.Framework.Sig

/-! # ARMv7 precomputed public RSA satisfies the shared API contract -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pd_contract_correct (s : State) (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre s) :
    ∃ tr t, Exec isa PdFn.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputedCheckedContract abi 56).post s t := by
  have input := pd_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := pdFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  intro nb length pre
  rw [pd_contract_length s h] at pre
  exact pdOutput_written input.minLength length pre post

theorem pd_contract_ct : ConstantTime isa (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pub PdFn.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := pd_contract_pre s hs
  have it := pd_contract_pre t ht
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4, p5, p6, _, p8, p9⟩ := hp
  rw [← p0, ← p1, ← p2, ← p4, ← p5, ← p6, ← p8, ← p9] at it
  rw [← p2, ← p3, ← p4, ← p5] at bytes
  obtain ⟨wordsEq, expEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range])
  have preEq := congrArg (List.map (BitVec.ofNat 64)) wordsEq
  have eEq := congrArg (List.map (BitVec.ofNat 8)) expEq
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at preEq eEq
  have first := VG.Proof.Bignum.wv_of_wordsAt (c := 0) (w := Spec.Rsa.modulusWords (s.gpr .r1).toNat) preEq
    (by rw [pd_contract_length s hs]; omega)
  have second := VG.Proof.Bignum.wv_of_wordsAt (c := Spec.Rsa.modulusWords (s.gpr .r1).toNat)
    (w := Spec.Rsa.modulusWords (s.gpr .r1).toNat) preEq (by rw [pd_contract_length s hs]; omega)
  rw [← read_eq_wv, ← read_eq_wv] at first second
  simp only [Nat.mul_zero, BitVec.add_zero] at first
  simp only [State.addr] at it
  rw [← first, ← second, ← eEq] at it
  exact (pdFn_ct s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1
end VG.Proof.Bignum.Arm
