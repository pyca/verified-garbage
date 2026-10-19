module

import VerifiedGarbage.Proof.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Bignum.Arm.PublicFnCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PublicInput
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Checked public RSA satisfies its shared contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem public_contract_pre (s : State) (h : (Spec.Rsa.publicCheckedContract abi 56).pre s) :
    PublicFnInput (stackArg s 4) (s.gpr .r0) (s.gpr .r2) (stackArg s 0) (stackArg s 2)
      (stackArg s 5).toNat (s.gpr .r3).toNat (stackArg s 1).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (s.gpr .r3).toNat) s := by
  sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, outWs, _, nWs, eWs, xWs, wsArgs,
    stackOut, stackN, stackE, stackX, stackWs, stackArgs, outFit, nFit, eFit, xFit, wsFit,
    valid, outLen, inputLen, ePositive, eLen, space⟩ := h
  rw [outLen] at wr outWs stackOut outFit
  rw [inputLen] at rd xWs stackX xFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  refine ⟨⟨?_, ?_⟩, valid.1, valid.2, space, ePositive, eLen,
    ⟨nFit, ?_, rfl⟩, ⟨eFit, ?_, rfl⟩, ⟨xFit, ?_, rfl⟩, outFit, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, ?_, stackFit, argFit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_comm] using wsFit
  · rw [wr]; simp [State.addr, Nat.mul_comm]
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [State.addr, Nat.mul_comm] using nWs
  · simpa only [State.addr, Nat.mul_comm] using eWs
  · simpa only [State.addr, Nat.mul_comm] using xWs
  · simpa only [State.addr, Nat.mul_comm] using outWs.symm
  · simp
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · unfold stackArg stackArgAddr
    rw [addr_add (by omega : s.sp.toNat + 4 * 4 < 2 ^ 32)]
  · simp only [stackArg, argAddr]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    unfold stackArg stackArgAddr
    rw [addr_add (by omega : s.sp.toNat + 4 * 1 < 2 ^ 32)]
  · unfold stackArg stackArgAddr
    rw [addr_add (by omega : s.sp.toNat + 4 * 2 < 2 ^ 32)]
  · rw [frame]; simpa only [State.addr, Nat.mul_comm] using stackWs
  · simpa only [State.addr, Nat.mul_comm] using wsArgs.symm
  · rw [frame]; exact stackN
  · rw [frame]; exact stackE
  · rw [frame]; exact stackX
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs

theorem public_contract_correct (s : State) (h : (Spec.Rsa.publicCheckedContract abi 56).pre s) :
    ∃ tr t, Exec isa PublicFn.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicCheckedContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := publicFn_ok s (public_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem public_contract_ct : ConstantTime isa (Spec.Rsa.publicCheckedContract abi 56).pre
    (Spec.Rsa.publicCheckedContract abi 56).pub PublicFn.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := public_contract_pre s hs
  have it := public_contract_pre t ht
  sig_pub [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, _, p8, p9⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p2, ← p3, ← p4, ← p5, ← p6, ← p8, ← p9] at it
  rw [← p2, ← p3, ← p4, ← p5] at byteEq
  obtain ⟨nEq, eEq⟩ := List.append_inj byteEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  simp only [State.addr] at it
  rw [← nEq, ← eEq] at it
  exact (publicFn_ct s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm
