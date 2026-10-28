module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCloseInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory

/-! # A supported candidate width draws the candidate and filters it by distance and trial division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def FilteredOutputs (E : Environment) (e : Nat) (p : Option Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.tooClose (8 * E.length) p (candidateValue E entropy) then
    Outputs E 2 E.length (List.replicate E.length 0) s
  else SieveOutputs E e entropy s

/-- After the code for the width: the status 2 or 3 written, or `eax = 4`
and the drawn candidate to go on. -/
def FrontOutputs (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) then
    Outputs E 2 E.length (List.replicate E.length 0) s
  else if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else Drawn E eBytes pBytes entropy s ∧ s.gpr .eax = 4

theorem drawn_front_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.Candidate.closeCheck E.width)
      (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 2)
        (.seq (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) (.seq (.block [.alu .cmp .eax (.imm 0)])
          (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 3) (.block [.mov .eax (.imm 4)]))))))) s fun t =>
      FrontOutputs E eBytes pBytes entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (close_ok v D) fun a ⟨Da, flag, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F.mutable
  have Kb : Keeps WitnessStep.clob s b := (K.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)
  · refine WP.ite false (by rw [cond, close]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (sieve_front_ok v Db) fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa only [FrontOutputs, close, Bool.false_eq_true, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, close]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 2) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [FrontOutputs, close, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

theorem sized_front_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.front E.width) s fun t =>
      FrontOutputs E eBytes pBytes entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.front VG.Impl.RsaKeyGen.X86.Candidate.importCandidate
  refine WP.seq (WP.mono (load_ok v I zeros enough) fun a ⟨D, F, K⟩ => ?_)
  refine WP.mono (drawn_front_ok v D) fun t ⟨output, Ft, Kt⟩ => ?_
  exact ⟨output, F.mutable.trans Ft, (K.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
