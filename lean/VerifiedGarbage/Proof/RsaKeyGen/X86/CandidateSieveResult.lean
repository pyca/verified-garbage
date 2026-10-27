module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory

/-! # Trial division: the status 3 written, or `eax = 4` to go on -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def SieveOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else ExponentOutputs E e entropy s

theorem sieve_front_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) (.seq (.block [.alu .cmp .eax (.imm 0)])
      (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 3) (.block [.mov .eax (.imm 4)])))) s fun t =>
      (if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
        Outputs E 3 E.length (List.replicate E.length 0) t
      else Drawn E eBytes pBytes entropy t ∧ t.gpr .eax = 4) ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (sieve_ok v D) fun a ⟨Da, flag, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F.mutable
  have Kb : Keeps WitnessStep.clob s b := (K.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
  · refine WP.ite false (by rw [cond, composite]) (fun bad => nomatch bad) (fun _ => ?_)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    refine ⟨⟨Db.keepMem v T.mem T.keeps (by decide) (by decide) T.syms, T.gpr⟩, by rw [T.mem]; exact Fb,
      Kb.widen T.keeps⟩
  · refine WP.ite true (by rw [cond, composite]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 3) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
