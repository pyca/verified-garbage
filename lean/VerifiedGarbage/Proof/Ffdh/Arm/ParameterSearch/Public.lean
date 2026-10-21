module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePre
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-! Read all search parameters and persistent policy from the existing public ARMv7 signature. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

structure SearchAbi (p : SearchParams) (s : State) : Prop extends
    VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateAbi p.c s where
  control : stackArg s 5 = p.control
  counter : s.mem.readW (State.addr p.control) 64 = BitVec.ofNat 64 p.attempts
  widthPolicy : s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length
  entropyPolicy : s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)

theorem searchPublic (s : State) (pre : (Spec.Ffdh.parameterSearchContract abi 232).pre s) :
    ∃ p, SearchAbi p s := by
  sig_pre [Spec.Ffdh.parameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, outUsed, outTape, outScratch, outControl, _, usedTape, usedScratch, usedControl, _,
    tapeScratch, tapeControl, scratchControl, _, _, _, _, _, _, _, _,
    outFit, usedFit, tapeFit, scratchFit, controlFit, lower, upper, width, generator, space,
    attemptsBound, widthPolicy, entropyPolicy, tapeBound⟩ := pre
  let rb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  have rbLength : rb.length = (stackArg s 2).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let q : VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams := {
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
  let p : SearchParams := {
    candidate := q, control := stackArg s 5,
    attempts := (s.mem.readW (State.addr (stackArg s 5)) 64).toNat
    attemptsBound := attemptsBound
    tapeBound := by rw [rbLength]; exact tapeBound
    controlFits := controlFit
    controlOutput := by
      change (⟨State.addr (stackArg s 5), 128⟩ : Region).Disjoint
        ⟨State.addr (s.gpr .r0), ((s.gpr .r3).toNat + 7) / 8⟩
      rw [← width]
      exact outControl.symm
    controlUsed := usedControl.symm
    controlScratch := by simpa only [Nat.mul_comm 8, State.addr] using scratchControl.symm
    controlTape := by rw [rbLength]; exact tapeControl.symm }
  refine ⟨p, ⟨?_, rfl, ?_, ?_, ?_⟩⟩
  · refine ⟨rfl, ?_, rfl, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
    · change s.gpr .r1 = BitVec.ofNat 32 (((s.gpr .r3).toNat + 7) / 8)
      rw [← width, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [p, q, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [p, q, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change stackArg s 2 = BitVec.ofNat 32 rb.length
      rw [rbLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [p, q, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) rb.length = rb
      rw [rbLength]
  · simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change s.mem.readW (off (State.addr (stackArg s 5)) 8) 64 =
      BitVec.ofNat 64 (((s.gpr .r3).toNat + 7) / 8)
    rw [← width]
    exact widthPolicy
  · exact entropyPolicy

end VG.Proof.Ffdh.Arm.ParameterSearch
