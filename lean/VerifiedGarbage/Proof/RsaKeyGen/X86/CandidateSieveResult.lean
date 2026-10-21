module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory

/-! # Trial-division rejection and coprimality testing compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def SieveOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else ExponentOutputs E e entropy s

theorem sieve_result_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.sieveCheck E.width montName mont roundName round) s fun t =>
      SieveOutputs E (Spec.Rsa.os2ip eBytes) entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.sieveCheck
  refine WP.seq (WP.mono (sieve_ok v D) fun a ⟨Da, flag, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F.mutable
  have Kb : Keeps WitnessStep.clob s b := (K.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
  · refine WP.ite false (by rw [cond, composite]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (exponent_result_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Db enough)
      fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa only [SieveOutputs, composite, Bool.false_eq_true, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, composite]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 3) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [SieveOutputs, composite, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
