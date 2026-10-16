module

public import VerifiedGarbage.Proof.Bignum.Arm.PcFn
public import VerifiedGarbage.Proof.Bignum.Arm.PcFnCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public precomputation satisfies the shared RSA contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pc_contract_pre (s : State) (h : (Spec.Rsa.publicPrecomputeContract abi 56).pre s) :
    PcFnInput (stackArg s 0) (s.gpr .r0) (s.gpr .r2) (stackArg s 1).toNat (s.gpr .r3).toNat s := by
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, outWs, _, srcWs, _, stackOut, stackSrc,
    stackWs, stackArgs, outFit, srcFit, wsFit, valid, outLen, space⟩ := h
  have outBytes : (s.gpr .r1).toNat * 8 = 16 * Spec.Rsa.modulusWords (s.gpr .r3).toNat := by
    rw [outLen]; simp only [Spec.Rsa.precomputedWords]; omega
  rw [outBytes] at wr outWs stackOut outFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  refine ⟨⟨⟨?_, ?_⟩, valid.1, valid.2, space, srcFit, ?_, ?_, outFit, ?_, ?_⟩,
    rfl, rfl, ?_, stackFit, argFit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_comm] using wsFit
  · rw [wr]; simp [State.addr, Nat.mul_comm]
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; exact List.mem_cons_self), Region.contains_self _ _⟩
  · simpa only [State.addr, Nat.mul_comm] using srcWs
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [State.addr, Nat.mul_comm] using outWs.symm
  · simp
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩
  · simp only [stackArg, argAddr]
  · rw [frame]; simpa only [State.addr, Nat.mul_comm] using stackWs
  · rw [frame]; exact stackSrc
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs

theorem pc_contract_correct (s : State) (h : (Spec.Rsa.publicPrecomputeContract abi 56).pre s) :
    ∃ tr t, Exec isa PcFn.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputeContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := pcFn_ok s (pc_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have outLen : (s.gpr .r1).toNat = 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat := by
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [outLen, BitVec.setWidth_append_eq_right]
  exact post

theorem pc_contract_ct : ConstantTime isa (Spec.Rsa.publicPrecomputeContract abi 56).pre
    (Spec.Rsa.publicPrecomputeContract abi 56).pub PcFn.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := pc_contract_pre s hs
  have it := pc_contract_pre t ht
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p2, ← p3, ← p4, ← p5] at it
  rw [← p2, ← p3] at byteEq
  exact (pcFn_ct s t tr1 tr2 u v ⟨⟨is, rfl⟩, ⟨it, byteEq.symm⟩, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm
