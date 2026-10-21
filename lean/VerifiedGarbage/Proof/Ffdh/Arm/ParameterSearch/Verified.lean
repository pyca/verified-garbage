module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Input
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Correct
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTFunction
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Sat
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! Complete correctness, public timing and satisfiability for native ARMv7 parameter generation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem constantTime (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    ConstantTime isa (Spec.Ffdh.sievedParameterSearchContract abi 232).pre (Spec.Ffdh.sievedParameterSearchContract abi 232).pub
      (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) := by
  intro s t traceS traceT u v hs ht pub runS runT
  obtain ⟨p, args⟩ := searchPublic s hs
  sig_pub [Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pub
  obtain ⟨sp, leak, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := pub
  obtain ⟨bytes, policy⟩ := List.append_inj leak (by
    simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, p6])
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have policyEq := congrArg (List.map (BitVec.ofNat 64)) policy
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at policyEq
  rw [← p9, args.control] at policyEq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero] at policyEq
  obtain ⟨word0, tail1⟩ := List.cons.inj policyEq
  obtain ⟨word1, tail2⟩ := List.cons.inj tail1
  obtain ⟨word2, _⟩ := List.cons.inj tail2
  have argsT : SearchAbi p t := {
    out := p0.symm.trans args.out
    width := p1.symm.trans args.width
    used := p2.symm.trans args.used
    bits := p3.symm.trans args.bits
    generator := p4.symm.trans args.generator
    tape := p5.symm.trans args.tape
    tapeLength := p6.symm.trans args.tapeLength
    base := p7.symm.trans args.base
    capacity := p8.symm.trans args.capacity
    bytes := by
      rw [← p5, ← p6, args.tape, args.tapeLength] at byteEq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.c.tapeCount] at byteEq
      exact byteEq.symm.trans args.bytes
    control := p9.symm.trans args.control
    counter := word0.symm.trans args.counter
    widthPolicy := word1.symm.trans args.widthPolicy
    entropyPolicy := word2.symm.trans args.entropyPolicy }
  exact ((function_ct backend) _ _ _ _ _ _
    ⟨p, searchInput hs args, searchInput ht argsT, sp⟩ runS runT).1

theorem verified (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate))
      (Spec.Ffdh.sievedParameterSearchContract abi 232) :=
  ⟨correct backend, constantTime backend, search_sat⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
