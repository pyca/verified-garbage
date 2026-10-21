module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateInput
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Spec.Ffdh.ScreenedContract

/-! The native candidate satisfies the public shared FFDH timing contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_contract_ct (v : RoundImpl) : ConstantTime isa (Spec.Ffdh.screenedParameterCandidateContract abi 184).pre
    (Spec.Ffdh.screenedParameterCandidateContract abi 184).pub (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) := by
  intro s t trS trT u z hs ht hp runS runT
  obtain ⟨p, args⟩ := candidatePublic s hs
  sig_pub [Spec.Ffdh.screenedParameterCandidateContract, Spec.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have argsT : CandidateAbi p t := {
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
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount] at byteEq
      exact byteEq.symm.trans args.bytes }
  exact ((candidateFn_ct v) _ _ _ _ _ _ ⟨p, candidateInput hs args, candidateInput ht argsT, sp⟩ runS runT).1

end VG.Proof.Ffdh.Arm.ParameterCandidate
