module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # Coprimality rejection, at a run-time width, and prepared primality testing for the width compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext (slot)

def ExponentOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Nat.gcd (candidateValue E entropy - 1) e = 1 then PrimalityOutputs E (candidateValue E entropy) entropy s
  else Outputs E 3 E.length (List.replicate E.length 0) s

/-- The width in `eax`, then Miller–Rabin for it. -/
theorem tested_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) s fun t =>
      PrimalityOutputs E (candidateValue E entropy) entropy t ∧ MutableFrame E s.mem t.mem ∧
        Keeps WitnessStep.clob s t := by
  have bounds := v.width_bounds
  have lengthBound : E.length < 2 ^ 32 := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  have space : 256 ≤ E.size := v.geometry.headerFit
  unfold VG.Impl.RsaKeyGen.X86.Candidate.tested VG.Impl.RsaKeyGen.X86.Candidate.width
  refine WP.seq (wp_movS (readSrc_sc D.input.scratch (d := 4) (by omega)) fun a A _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun b B => WP.block_nil ?_)
  have M : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have width : b.gpr .eax = BitVec.ofNat 32 E.width := by
    rw [B.gpr, A.gpr, D.input.header 1 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    change (E.length % 2 ^ 32) / 8 = E.width % 2 ^ 32
    rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt (by omega : E.width < 2 ^ 32)]
    rfl
  refine dispatch_ok width (by omega) VG.Impl.RsaKeyGen.X86.Candidate.widths ?_ ?_ fun c C => ?_
  · exact List.mem_map.mpr ⟨E.width - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w mem
    obtain ⟨i, index, rfl⟩ := List.mem_map.mp mem
    have bound := List.mem_range.mp index
    omega
  have Mc : c.mem = s.mem := C.mem.trans M
  have Kc : Keeps [.eax] s c := K.widen (C.keeps [])
  refine WP.mono (prepared_result_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (D.keepMem v Mc Kc (by decide) (by decide) (C.syms.trans (B.syms.trans A.syms))) (by rw [Mc]; exact minusOne) enough)
    fun t ⟨output, F, Kt⟩ => ?_
  rw [Mc] at F
  exact ⟨output, F, (Kc.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

theorem exponent_result_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
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
