module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn

/-! # Public width dispatch selects the verified candidate implementation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem dispatch_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) (width : s.gpr .eax = BitVec.ofNat 32 E.width)
    (widths : List Nat) (member : E.width ∈ widths) (bounded : ∀ w ∈ widths, w < 2 ^ 32) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.dispatch montName mont roundName round widths) s fun t =>
      FilteredOutputs E (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  induction widths generalizing s with
  | nil => cases member
  | cons w rest ih =>
    unfold VG.Impl.RsaKeyGen.X86.Candidate.dispatch
    refine WP.seq (wp_cmpS rfl fun a A Z => WP.block_nil ?_)
    have Ia := I.keepMem v A.mem (A.keeps []) (by decide) (by decide) A.syms
    have za : Spec.Rsa.bytesAt a.mem (E.out.setWidth 64) E.length = List.replicate E.length 0 := by rw [A.mem]; exact zeros
    have condition : isa.eval .e a = some (decide (E.width = w)) := by
      change a.zf = _
      rw [Z, width]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      rw [BitVec.sub_eq_iff_eq_add]
      change (BitVec.ofNat 32 E.width = 0#32 + BitVec.ofNat 32 w) ↔ E.width = w
      rw [BitVec.zero_add, ← BitVec.toNat_inj]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (bounded w List.mem_cons_self), Nat.mod_eq_of_lt (by have := v.width_bounds.2; omega)]
    by_cases same : E.width = w
    · refine WP.ite true (by rw [condition, decide_eq_true same]) (fun _ => ?_) (fun bad => nomatch bad)
      rw [← same]
      refine WP.mono (sized_result_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Ia za enough)
        fun t ⟨output, F, K⟩ => ?_
      rw [A.mem] at F
      exact ⟨output, F, (A.keeps WitnessStep.clob).trans K⟩
    · refine WP.ite false (by rw [condition, decide_eq_false same]) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.mono (ih Ia za (by rw [A.gpr]; exact width) (List.mem_cons.mp member |>.resolve_left same)
        (fun j mem => bounded j (List.mem_cons_of_mem _ mem))) fun t ⟨output, F, K⟩ => ?_
      rw [A.mem] at F
      exact ⟨output, F, (A.keeps WitnessStep.clob).trans K⟩

end VG.Proof.RsaKeyGen.X86.Candidate
