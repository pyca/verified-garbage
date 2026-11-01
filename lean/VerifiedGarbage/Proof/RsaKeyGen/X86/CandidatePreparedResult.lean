module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
/-! # Prepared testing and finish implement exactly the complete primality result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFinishResult.lean`, which only this module imported.
section

/-! # The prepared status selects exactly the matching native finish path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

def ResultOutputs (E : Environment) (c tag count : Nat) (s : State) : Prop :=
  Outputs E tag (if tag = 0 then 0 else count)
    (if tag = 1 then Spec.Rsa.i2osp c E.length else List.replicate E.length 0) s

theorem finish_result_ok {E : Environment} (v : E.Valid) {c tag : Nat} {s : State}
    (S : FinishReady E c s) (tags : tag = 0 ∨ tag = 1 ∨ tag = 3)
    (status : w32 s.mem E.base 168 = tag) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult E.width) s fun t =>
      ResultOutputs E c tag (w32 s.mem E.base 152) t ∧ MutableFrame E s.mem t.mem ∧
      Keeps WitnessStep.clob s t := by
  have tagBound : tag < 2 ^ 32 := by omega
  have statusWord : s.mem.readW (off E.base 168) 32 = BitVec.ofNat 32 tag := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt tagBound]
    exact status
  have header : 172 ≤ E.size := by have := S.1.header; have := v.geometry.headerFit; change 256 ≤ E.size at this; omega
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult
  refine WP.seq (wp_movS (readSrc_sc S.1.scratch (d := 168) (by omega)) fun a A _ =>
    wp_cmpS rfl fun b B Z => WP.block_nil ?_)
  have M : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := S.keepMem M K (by decide) (by decide)
  have value : b.gpr .eax = BitVec.ofNat 32 tag := by rw [(B.keeps []).1 .eax (by decide), A.gpr, statusWord]
  have condition : isa.eval .e b = some (decide (tag = 1)) := by
    change b.zf = _
    rw [Z, A.gpr, statusWord]
    rcases tags with rfl | rfl | rfl <;> decide
  by_cases accepted : tag = 1
  · rw [accepted]
    refine WP.ite true (by rw [condition, decide_eq_true accepted]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_prime_ok v Sb) fun t ⟨output, F, Kt⟩ => ?_
    rw [M] at output F
    exact ⟨output, F, (K.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite false (by rw [condition, decide_eq_false accepted]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.seq (wp_cmpS rfl fun d D Z0 => WP.block_nil ?_)
    have Md : d.mem = s.mem := D.mem.trans M
    have Kd : Keeps [.eax] s d := K.widen (D.keeps [])
    have Sd := S.keepMem Md Kd (by decide) (by decide)
    have condition0 : isa.eval .e d = some (decide (tag = 0)) := by
      change d.zf = _
      rw [Z0, value]
      rcases tags with rfl | rfl | rfl <;> decide
    by_cases exhausted : tag = 0
    · rw [exhausted]
      refine WP.ite true (by rw [condition0, decide_eq_true exhausted]) (fun _ => ?_) (fun bad => nomatch bad)
      refine WP.mono (finish_none_ok v Sd) fun t ⟨output, F, Kt⟩ => ?_
      rw [Md] at F
      exact ⟨output, F, (Kd.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
    · have rejected : tag = 3 := by omega
      rw [rejected]
      refine WP.ite false (by rw [condition0, decide_eq_false exhausted]) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.mono (finish_used_ok (status := 3) v Sd) fun t ⟨output, F, Kt⟩ => ?_
      rw [Md] at output F
      exact ⟨output, F, (Kd.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def PrimalityOutputs (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop :=
  match Spec.RsaKeyGen.primalityTest c (entropy.drop E.length) with
  | none => Outputs E 0 0 (List.replicate E.length 0) s
  | some (prime, rest) => Outputs E (if prime then 1 else 3) (entropy.length - rest.length)
      (if prime then Spec.Rsa.i2osp c E.length else List.replicate E.length 0) s

/-- Miller–Rabin's result is the same code at every width. -/
theorem mrResult_zero (w : Nat) :
    VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult 0 = VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult w := by
  simp only [VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult, VG.Impl.RsaKeyGen.X86.CandidateFinish.prime,
    VG.Proof.RsaKeyGen.X86.ExponentRt.slot0_eq]

/-- Preparation with the exponent at the run-time width, the witnesses, and
the result. -/
theorem tested_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) s fun t =>
      PrimalityOutputs E (candidateValue E entropy) entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.tested
  rw [mrResult_zero E.width]
  refine WP.seq (WP.mono (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v D minusOne enough)
    fun a ⟨value, result, W, F, K⟩ => ?_)
  have ready := D.finishReady_after_test v value W F K
  have frame : MutableFrame E s.mem a.mem := F.mutable
  rw [MillerRabinLoop.Result, v.test_eq] at result
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop (8 * E.width)) with
    | none => w32 a.mem E.base 168 = 0
    | some (prime, rest) => w32 a.mem E.base 168 = (if prime then 1 else 3) ∧
        w32 a.mem E.base 152 = entropy.length - rest.length) at result
  rw [v.length_eq] at result
  cases test : Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length) with
  | none =>
    rw [test] at result
    refine WP.mono (finish_result_ok v ready (Or.inl rfl) result) fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩
  | some pr =>
    obtain ⟨prime, rest⟩ := pr
    rw [test] at result
    cases prime
    · refine WP.mono (finish_result_ok v ready (Or.inr (Or.inr rfl)) result.1) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [ResultOutputs, result.2] at output
      exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩
    · refine WP.mono (finish_result_ok v ready (Or.inr (Or.inl rfl)) result.1) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [ResultOutputs, result.2] at output
      exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
