module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInput
/-! # Trial division: the status 3 written, or `eax = 4` to go on -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateExponentResult.lean`, which only this module imported.
section

/-! # Coprimality rejection, at a run-time width, and prepared primality testing for the width compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext (slot)

def ExponentOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Nat.gcd (candidateValue E entropy - 1) e = 1 then PrimalityOutputs E (candidateValue E entropy) entropy s
  else Outputs E 3 E.length (List.replicate E.length 0) s

theorem exponent_result_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck montName mont roundName round) s fun t =>
      ExponentOutputs E (Spec.Rsa.os2ip eBytes) entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck
  refine WP.seq (WP.mono (exponent_ok v D) fun a ⟨Da, flag, saved, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, cond, _⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F.mutable
  have Kb : Keeps WitnessStep.clob s b := (K.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  by_cases good : Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) = 1
  · refine WP.ite false (by rw [cond, decide_eq_true good]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Db
      (by rw [B.mem]; exact saved) enough) fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa only [ExponentOutputs, good, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, decide_eq_false good]; rfl) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 3) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [ExponentOutputs, good, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def SieveOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else ExponentOutputs E e entropy s

end VG.Proof.RsaKeyGen.X86.Candidate
