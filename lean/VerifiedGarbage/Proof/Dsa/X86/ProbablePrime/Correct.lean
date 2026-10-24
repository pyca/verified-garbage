module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Framed
public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState

/-! # The probable-prime test meets the shared contract's postcondition -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
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
  sig_post [contract, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  obtain ⟨status, used⟩ := R
  refine ⟨status, ?_, fun b rest same => used b rest same⟩
  intro i index outside
  have far := outside _ List.mem_cons_self
  change i < 0 ∨ 0 + (callEnvironment bits s).scratch ≤ i at far
  exact T i (by omega) index

end VG.Proof.Dsa.X86.ProbablePrime
