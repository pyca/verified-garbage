module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithFn
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallContract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! The shared reviewed Montgomery contract for a supplied dispatcher. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (wOf Operand)

theorem montCallWith_contract_correct (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) (s : State) (h : (Proof.Rsa.Mont.mulContract abi 40).pre s) :
    ∃ tr t, Exec isa (MontCallWith.code arithmetic) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.Mont.mulContract abi 40).post s t := by
  obtain ⟨input, ho, ha, hb⟩ := montCall_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := montCallWithFn_ok arithmetic law s input ho ha hb
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have argValue : stackArg s 0 = callStackB s := by simp [stackArg, stackArgAddr, callStackB]
  rw [argValue]
  exact post

theorem montCallWith_contract_ct (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) : ConstantTime isa (Proof.Rsa.Mont.mulContract abi 40).pre
    (Proof.Rsa.Mont.mulContract abi 40).pub (MontCallWith.code arithmetic) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨is, ho, ha, hb⟩ := montCall_contract_pre s hs
  obtain ⟨it, _, _, _⟩ := montCall_contract_pre t ht
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, width, p0, p1, p2, p3, pb⟩ := hp
  change [wOf s.mem (State.addr (s.gpr .r0))] = [wOf t.mem (State.addr (t.gpr .r0))] at width
  have wb := List.singleton_inj.mp width
  have bb : callStackB s = callStackB t := by simpa only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, callStackB] using pb
  rw [← wb, ← p0, ← p1, ← p2, ← p3, ← bb] at it
  exact (montCallWithFn_ct arithmetic law ho ha hb s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

theorem montCallWith_verified (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) :
    Verified target (MontCallWith.code arithmetic) (Proof.Rsa.Mont.mulContract abi 40) :=
  ⟨montCallWith_contract_correct arithmetic law, montCallWith_contract_ct arithmetic law,
    montCall_contract_sat⟩

theorem montCallWith_stack (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) :
    FrameStack.armStack (MontCallWith.code arithmetic) ≤ 40 := by
  simp only [MontCallWith.code, FrameStack.armStack, law.stack]
  decide

end VG.Proof.Bignum.Arm
