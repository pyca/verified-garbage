module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ConstantTime
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Satisfiable
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.NoSp
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Framed
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
/-! # DSA's probable-prime test on i686 is verified -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ProbablePrime/Correct.lean`, which only this module imported.
section

/-! # The probable-prime test meets the shared contract's postcondition -/

section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) {bits : Nat} (b : Bits bits)
    (s : State) (h : (contract bits).pre s) :
    ∃ trace t, Exec isa (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) s trace t ∧
      abiPreserved s t ∧ (contract bits).post s t := by
  have F := call_facts h
  have v := F.valid b
  obtain ⟨trace, t, run, preserved, R, T⟩ := framed_ok montVerified montNoSp montStack roundVerified roundNoSp
    roundStack v (F.entry b) F.odd F.length F.low (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [F.workspaceRegion]; exact F.retWs
      · exact F.retUsed)
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  obtain ⟨status, used⟩ := R
  refine ⟨status, ?_, fun b rest same => used b rest same⟩
  intro i index outside
  have far := outside _ List.mem_cons_self
  change i < 0 ∨ 0 + (callEnvironment bits s).scratch ≤ i at far
  exact T i (by omega) index

end VG.Proof.Dsa.X86.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86

theorem verified {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) (bits : Nat)
    (low : 64 ≤ bits := by decide) (high : bits ≤ 4096 := by decide) (whole : bits % 32 = 0 := by decide) :
    Verified target (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) (contract bits) :=
  ⟨correct montVerified montNoSp montStack roundVerified roundNoSp roundStack ⟨low, high, whole⟩,
    constantTime montVerified montNoSp montStack roundVerified roundNoSp roundStack ⟨low, high, whole⟩,
    satisfiable ⟨low, high, whole⟩⟩

theorem code_all {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (bits : Nat) (montName roundName : String) :
    (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round).all (fun i => !isa.writesSp i) = true := by
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  refine Code.all_of_allInstrs ?_
  rw [equal]
  exact VG.Proof.RsaKeyGen.X86.CandidateNoSp.checked (code_noSp Hm Hr bits montName roundName)

end VG.Proof.Dsa.X86.ProbablePrime
