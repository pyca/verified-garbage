module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Public size dispatch reveals no candidate or private-prime values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.RsaKeyGen

theorem dispatch_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (widths : List Nat) (member : E.width ∈ widths) (bounded : ∀ w ∈ widths, w < 2 ^ 32) :
    RelCT isa (WithValue (ClearedPair E eBytes pBytes qBytes rBytes sBytes) (BitVec.ofNat 32 E.width))
      (VG.Impl.RsaKeyGen.X86.Candidate.dispatch montName mont roundName round widths) (fun _ _ => True) := by
  induction widths with
  | nil => cases member
  | cons w rest ih =>
    unfold VG.Impl.RsaKeyGen.X86.Candidate.dispatch
    have compare := compare_value_trace (P := ClearedPair E eBytes pBytes qBytes rBytes sBytes) (BitVec.ofNat 32 E.width) (BitVec.ofNat 32 w)
      (fun _ _ _ _ P U Z => P.keepFlags v U Z)
    rw [width_comparison (by have := v.width_bounds.2; omega) (bounded w List.mem_cons_self)] at compare
    by_cases same : E.width = w
    · rw [decide_eq_true same] at compare
      refine RelCT.seq compare (branch_true ?_)
      rw [← same]
      exact (sized_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length rEnough enough leak).mono
        (fun _ _ P => P.1) (fun _ _ _ => trivial)
    · rw [decide_eq_false same] at compare
      exact RelCT.seq compare (branch_false (ih (List.mem_cons.mp member |>.resolve_left same)
        (fun j mem => bounded j (List.mem_cons_of_mem _ mem))))

end VG.Proof.RsaKeyGen.X86.Candidate
