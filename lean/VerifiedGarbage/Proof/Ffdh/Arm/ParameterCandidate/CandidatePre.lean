module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! Instantiate all candidate bounds from the public parameter-candidate contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm

structure CandidateAbi (p : CandidateParams) (s : State) : Prop where
  out : s.gpr .r0 = p.out
  width : s.gpr .r1 = BitVec.ofNat 32 p.length
  used : s.gpr .r2 = p.usedPtr
  bits : s.gpr .r3 = BitVec.ofNat 32 p.bits
  generator : stackArg s 0 = BitVec.ofNat 32 p.generator
  tape : stackArg s 1 = p.tape
  tapeLength : stackArg s 2 = BitVec.ofNat 32 p.bytes.length
  base : stackArg s 3 = p.base
  capacity : stackArg s 4 = BitVec.ofNat 32 p.capacity
  bytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes

theorem candidatePublic (s : State) (pre : (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre s) :
    ∃ p, CandidateAbi p s := by
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, outUsed, outTape, outScratch, _, usedTape, usedScratch, _, tapeScratch, _,
    _, _, _, _, _, outFit, usedFit, tapeFit, scratchFit, lower, upper, width, generator, space⟩ := pre
  let rb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  have rbLength : rb.length = (stackArg s 2).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : CandidateParams := {
    out := s.gpr .r0, usedPtr := s.gpr .r2, tape := stackArg s 1, base := stackArg s 3
    bits := (s.gpr .r3).toNat, generator := (stackArg s 0).toNat, capacity := (stackArg s 4).toNat, bytes := rb
    minBits := lower, maxBits := upper, generatorAllowed := generator
    space := by rw [← width]; exact space
    scratchFits := by simpa only [Nat.mul_comm 8] using scratchFit
    outputFits := by rw [← width]; exact outFit
    usedFits := usedFit
    tapeFits := by rw [rbLength]; exact tapeFit
    tapeCount := by rw [rbLength]; exact (stackArg s 2).isLt
    outputUsed := by rw [← width]; exact outUsed
    outputScratch := by rw [← width]; simpa only [Nat.mul_comm 8, State.addr] using outScratch
    outputTape := by rw [← width, rbLength]; exact outTape
    usedScratch := by simpa only [Nat.mul_comm 8, State.addr] using usedScratch
    usedTape := by rw [rbLength]; exact usedTape
    tapeScratch := by rw [rbLength]; simpa only [Nat.mul_comm 8, State.addr] using tapeScratch }
  refine ⟨p, rfl, ?_, rfl, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · change s.gpr .r1 = BitVec.ofNat 32 (((s.gpr .r3).toNat + 7) / 8)
    rw [← width, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change stackArg s 2 = BitVec.ofNat 32 rb.length
    rw [rbLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) rb.length = rb
    rw [rbLength]

end VG.Proof.Ffdh.Arm.ParameterCandidate
