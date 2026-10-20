module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlPreserve
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchControlMemory

/-! # Retry-counter updates preserve both the p-search invariant and its final result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem PSearchMemory.control {P : PSearchPlan} {W : Nat → BitVec 32} {s t : State}
    (R : PSearchMemory P W s) (O : Outside (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s.mem t.mem)
    (K : Keeps [.eax, .ecx] s t) : PSearchMemory P W t := by
  have qw := P.context.geometry.qWidth
  refine ⟨R.context.control O K (by decide),
    R.seed.keep ((controlOutside_frame O).sub (control_mutable _)) P.seed.parameterApart K, R.source, ?_, R.seedUsed⟩
  rw [control_bytes O (by unfold q usedBytes domainCheck; omega)
    (by unfold q VG.Impl.Dsa.Generation.Layout.control; omega), R.qval]

theorem PSearchAccepted.control {P : PSearchPlan} {value : Nat} {s t : State}
    (R : PSearchAccepted P value s) (O : Outside (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s.mem t.mem)
    (K : Keeps [.eax, .ecx] s t) : PSearchAccepted P value t := by
  have pw := P.context.geometry.width
  refine ⟨R.domain, R.prepared.frame (controlOutside_frame O) (control_arithmeticApart _) K (by decide), ?_, ?_⟩
  · rw [control_bytes O (by unfold p usedBytes domainCheck; omega)
      (by unfold p VG.Impl.Dsa.Generation.Layout.control; omega), R.pBytes]
  · rw [control_bytes O (by unfold exponent usedBytes domainCheck; omega)
      (by unfold exponent VG.Impl.Dsa.Generation.Layout.control; omega), R.exponentBytes]

theorem pSearchInvariant_stable (P : PSearchPlan) (expected : Option (Option Nat × List Byte)) (initial : State)
    (counter : Nat) : SearchPayload (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control)
      (PSearchInvariant P expected initial counter) := by
  rintro s t ⟨W, used, R, cursor, bound, retry, remaining, Oi, rd, wr⟩ O K
  exact ⟨W, used, R.control O K, cursor, bound, retry, remaining,
    Oi.trans ((controlOutside_frame O).sub (control_mutable _)), K.2.1.trans rd, K.2.2.trans wr⟩

theorem pSearchFinished_stable (P : PSearchPlan) (expected : Option (Option Nat × List Byte)) (initial : State) :
    SearchPayload (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) (PSearchFinished P expected initial) := by
  rintro s t ⟨W, used, R, cursor, bound, result, Oi, rd, wr⟩ O K
  refine ⟨W, used, R.control O K, cursor, bound, ?_,
    Oi.trans ((controlOutside_frame O).sub (control_mutable _)), K.2.1.trans rd, K.2.2.trans wr⟩
  rcases result with failed | rejected | ⟨value, status, expected, accepted⟩
  · exact .inl failed
  · exact .inr (.inl rejected)
  · exact .inr (.inr ⟨value, status, expected, accepted.control O K⟩)

theorem pSearch_done {P : PSearchPlan} {expected : Option (Option Nat × List Byte)} {initial s : State}
    (I : PSearchInvariant P expected initial (32 * P.context.geometry.pLen) s) : PSearchFinished P expected initial s := by
  obtain ⟨W, used, R, cursor, bound, retry, remaining, O, rd, wr⟩ := I
  have pw := P.context.geometry.width
  have done := VG.Proof.Dsa.Generation.primeSearch_done (l := 8 * P.context.geometry.pLen)
    (n := 8 * P.context.geometry.qLen) (q := P.qvalue) (counter := 32 * P.context.geometry.pLen)
    P.seed.bytes (P.context.witnesses.bytes.drop used) (by omega)
  exact ⟨W, used, R, cursor, bound, .inr (.inl ⟨retry (by omega), remaining.trans done⟩), O, rd, wr⟩
end VG.Proof.Dsa.X86.Generation
