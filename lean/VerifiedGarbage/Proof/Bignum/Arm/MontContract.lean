module

import VerifiedGarbage.Proof.Bignum.Arm.MontFn
import VerifiedGarbage.Proof.Bignum.Arm.MontFnCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.Entry

/-! # The shared RSA Montgomery contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (wOf Operand)

abbrev stackB (s : State) : BitVec 32 := s.mem.readW (State.addr s.sp) 32

theorem mont_contract_pre (s : State) (h : (Spec.Rsa.Mont.mulContract abi 36).pre s) :
    FnInput (s.gpr .r0) (s.gpr .r1).toNat (wOf s.mem (State.addr (s.gpr .r0)))
      (s.gpr .r2).toNat (s.gpr .r3).toNat (stackB s).toNat s ∧
      Operand (s.gpr .r2).toNat ∧ Operand (s.gpr .r3).toNat ∧ Operand (stackB s).toNat := by
  sig_pre [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argValue : stackArg s 0 = stackB s := by simp [stackArg, argAddr]
  rw [argAddr, argValue] at h
  obtain ⟨stackFit, _, rd, wr, _, stackWs, stackArgSep, nowrap, layout, ho, ha, hb, inverse, operand⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, layout, rfl, rfl, ?_, ?_, ?_, inverse, operand, stackFit, ?_, ?_, ?_⟩, ho, ha, hb⟩
  · simpa only [Nat.mul_comm] using nowrap
  · rw [wr]; simp only [List.mem_singleton, State.addr, Nat.mul_comm]
  · simp
  · simp
  · simp
  · refine ⟨⟨State.addr s.sp, 4⟩, List.mem_append_left _ ?_, ?_⟩
    · rw [rd]; simp
    · simp [Region.Contains]
  · unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
    simpa only [State.addr, Nat.mul_comm] using stackWs
  · unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
    exact stackArgSep


theorem mont_contract_correct (s : State) (h : (Spec.Rsa.Mont.mulContract abi 36).pre s) :
    ∃ tr t, Exec isa MontFn.mul s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.Mont.mulContract abi 36).post s t := by
  obtain ⟨input, ho, ha, hb⟩ := mont_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := montFn_ok s input ho ha hb
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have argValue : stackArg s 0 = stackB s := by simp [stackArg, stackArgAddr, stackB]
  rw [argValue]
  exact post

theorem mont_contract_ct : ConstantTime isa (Spec.Rsa.Mont.mulContract abi 36).pre
    (Spec.Rsa.Mont.mulContract abi 36).pub MontFn.mul := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨is, ho, ha, hb⟩ := mont_contract_pre s hs
  obtain ⟨it, _, _, _⟩ := mont_contract_pre t ht
  sig_pub [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, width, p0, p1, p2, p3, pb⟩ := hp
  change [wOf s.mem (State.addr (s.gpr .r0))] = [wOf t.mem (State.addr (t.gpr .r0))] at width
  have wb := List.singleton_inj.mp width
  have bb : stackB s = stackB t := by simpa only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, stackB] using pb
  rw [← wb, ← p0, ← p1, ← p2, ← p3, ← bb] at it
  exact (montFn_ct ho ha hb s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm
