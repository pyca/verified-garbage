module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Test
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore

/-! # A drawn candidate enters the complete prepared test with its original entropy snapshot -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem test_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
      (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round)) s fun t =>
      val32 t.mem E.base (slot E.width 0) (2 * E.width) = candidateValue E entropy ∧
      MillerRabinLoop.Result (E.parameters entropy) t ∧
      WorkspaceFrame E.geometry (CandidateTest.ranges E.geometry) s.mem t.mem ∧
      WorkFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have top : 2 ^ (64 * E.width - 1) ≤ candidateValue E entropy := by
    have lower := (candidate_shape v entropy).2.1
    have width := v.width_bounds.1
    have eqPower : 2 ^ (64 * E.width - 1) = 2 ^ (64 * E.width - 2) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [eqPower]
    omega
  refine WP.mono (MrExponentRt.tested_frame_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (v.parameters_valid entropy D.input.memory.entropyLength) v.width_bounds.1 v.width_bounds.2 rfl rfl rfl rfl
    D.input.scratch (D.input.capacity_eq v)
    (by change E.p - 28#32 = s.gpr .esp - 28#32; rw [D.input.stack])
    (by rw [← Prepared.slot_eq]; exact D.candidate) (by rw [← Prepared.slot_eq]; exact minusOne)
    top D.input.memory.randRead D.input.memory.entropy D.input.rand_eq (D.input.randLength_eq v)
    (by change w32 s.mem E.base 152 = 8 * E.width; rw [D.used, v.length_eq])
    (by change 8 * E.width ≤ E.randLength; rw [v.length_eq]; exact enough)
    (by
      change s.mem.readW (off E.base (4 * 1)) 32 = BitVec.ofNat 32 (8 * E.width)
      rw [D.input.header 1 (by decide)]
      change BitVec.ofNat 32 E.length = _
      rw [v.length_eq])
    (by rw [D.input.stack]; exact v.low) (by rw [D.input.stack]; exact v.workspaceStack)
    (by
      rw [D.input.stack]
      exact (v.stackFar E.randRegion (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right (below_sub (by decide) v.low)))
    fun t ⟨value, result, W, F, K⟩ => ?_
  rw [D.input.stack] at F
  refine ⟨?_, result, W, F, K⟩
  rw [← Prepared.slot_eq] at value
  exact value

end VG.Proof.RsaKeyGen.X86.Candidate
