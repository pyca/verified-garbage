module

public import VerifiedGarbage.Proof.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdFnCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Checked public RSA satisfies its shared contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pd_contract_pre (s : State) (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre s) :
    PdFnInput (stackArg s 4) (s.gpr .r0) (s.gpr .r2) (stackArg s 0) (stackArg s 2)
      (stackArg s 5).toNat (s.gpr .r1).toNat (stackArg s 1).toNat
      (s.mem.read (State.addr (s.gpr .r2)) (8 * Spec.Rsa.modulusWords (s.gpr .r1).toNat)).toNat
      (s.mem.read (VG.Proof.Mont.off (State.addr (s.gpr .r2)) (8 * Spec.Rsa.modulusWords (s.gpr .r1).toNat)) (8 * Spec.Rsa.modulusWords (s.gpr .r1).toNat)).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (s.gpr .r1).toNat) s := by
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, outWs, _, nWs, eWs, xWs, wsArgs,
    stackOut, stackN, stackE, stackX, stackWs, stackArgs, outFit, nFit, eFit, xFit, wsFit,
    valid, preLen, inputLen, ePositive, eLen, space⟩ := h
  rw [preLen] at rd nWs stackN nFit
  have preSize : Spec.Rsa.precomputedWords (s.gpr .r1).toNat * 8 = 16 * Spec.Rsa.modulusWords (s.gpr .r1).toNat := by
    simp only [Spec.Rsa.precomputedWords]; omega
  rw [preSize] at rd nWs stackN nFit
  rw [inputLen] at rd xWs stackX xFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  refine ⟨⟨?_, ?_⟩, valid.1, valid.2, space, ePositive, eLen,
    nFit, ?_, rfl, rfl, ⟨eFit, ?_, rfl⟩, ⟨xFit, ?_, rfl⟩, outFit, ?_, ?_, ?_, ?_, ?_,
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

theorem pd_contract_length (s : State) (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre s) :
    (s.gpr .r3).toNat = 2 * Spec.Rsa.modulusWords (s.gpr .r1).toNat := by
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, preLen, _⟩ := h
  exact preLen

end VG.Proof.Bignum.Arm
