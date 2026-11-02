module

import VerifiedGarbage.Proof.Bignum.Arm.MontCallFn
import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Arm.MontVerified
meta import VerifiedGarbage.Proof.Bignum.Arm.MontVerified
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Rsa.MontContract

/-! # The shared RSA Montgomery contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (wOf Operand)

abbrev callStackB (s : State) : BitVec 32 := s.mem.readW (State.addr s.sp) 32


theorem montCall_contract_pre (s : State) (h : (Proof.Rsa.Mont.mulContract abi 40).pre s) :
    CallInput (s.gpr .r0) (s.gpr .r1).toNat (wOf s.mem (State.addr (s.gpr .r0)))
      (s.gpr .r2).toNat (s.gpr .r3).toNat (callStackB s).toNat s ∧
      Operand (s.gpr .r2).toNat ∧ Operand (s.gpr .r3).toNat ∧ Operand (callStackB s).toNat := by
  sig_pre [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argValue : stackArg s 0 = callStackB s := by simp [stackArg, argAddr]
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


theorem montCall_contract_correct (s : State) (h : (Proof.Rsa.Mont.mulContract abi 40).pre s) :
    ∃ tr t, Exec isa MontCall.code s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.Mont.mulContract abi 40).post s t := by
  obtain ⟨input, ho, ha, hb⟩ := montCall_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := montCallFn_ok s input ho ha hb
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have argValue : stackArg s 0 = callStackB s := by simp [stackArg, stackArgAddr, callStackB]
  rw [argValue]
  exact post

theorem montCall_contract_ct : ConstantTime isa (Proof.Rsa.Mont.mulContract abi 40).pre
    (Proof.Rsa.Mont.mulContract abi 40).pub MontCall.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨is, ho, ha, hb⟩ := montCall_contract_pre s hs
  obtain ⟨it, _, _, _⟩ := montCall_contract_pre t ht
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, width, p0, p1, p2, p3, pb⟩ := hp
  change [wOf s.mem (State.addr (s.gpr .r0))] = [wOf t.mem (State.addr (t.gpr .r0))] at width
  have wb := List.singleton_inj.mp width
  have bb : callStackB s = callStackB t := by simpa only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, callStackB] using pb
  rw [← wb, ← p0, ← p1, ← p2, ← p3, ← bb] at it
  exact (montCallFn_ct ho ha hb s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

theorem montCall_contract_sat : ∃ s, (Proof.Rsa.Mont.mulContract abi 40).pre s := by
  sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [montSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using montSatState

theorem montCall_verified : Verified target MontCall.code (Proof.Rsa.Mont.mulContract abi 40) :=
  ⟨montCall_contract_correct, montCall_contract_ct, montCall_contract_sat⟩

theorem montCallUmaal_verified :
    Verified target (umaalArithmetic MontCall.code) (Proof.Rsa.Mont.mulContract abi 40) :=
  umaalArithmetic_verified montCall_verified

end VG.Proof.Bignum.Arm
