module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeIteration

/-! # A seed phase either exhausts witnesses, rejects the seed, or returns a packed domain -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def PhaseResult (P : SearchContextPlan) (seedUsed : BitVec 32)
    (expected : Option (Option Spec.Dsa.Params × List Byte)) (initial s : State) : Prop :=
  ∃ W used, SearchContext P W s ∧ W 10 = seedUsed ∧ W 16 = BitVec.ofNat 32 used ∧ used ≤ P.witnesses.bytes.length ∧
    ((W 19 = 0 ∧ expected = none) ∨ (W 19 = 3 ∧ expected = some (none, P.witnesses.bytes.drop used)) ∨
      ∃ params, W 19 = 1 ∧ expected = some (some params, P.witnesses.bytes.drop used) ∧
        Spec.Rsa.bytesAt s.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) =
          Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen params) ∧
    Frame (parameterWrites P.geometry) initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

theorem PhaseResult.prepend {P : SearchContextPlan} {seedUsed : BitVec 32}
    {expected : Option (Option Spec.Dsa.Params × List Byte)} {initial a t : State}
    (R : PhaseResult P seedUsed expected a t) (O : Frame (parameterWrites P.geometry) initial.mem a.mem)
    (rd : a.rd = initial.rd) (wr : a.wr = initial.wr) : PhaseResult P seedUsed expected initial t := by
  obtain ⟨W, used, context, seed, cursor, bound, result, tail, rdt, wrt⟩ := R
  exact ⟨W, used, context, seed, cursor, bound, result, O.trans tail, rdt.trans rd, wrt.trans wr⟩

theorem phaseResult_stable (P : SearchContextPlan) (seedUsed : BitVec 32)
    (expected : Option (Option Spec.Dsa.Params × List Byte)) (initial : State) :
    TapeStable (PhaseResult P seedUsed expected initial) := by
  rintro s t ⟨W, used, R, seed, cursor, bound, result, O, rd, wr⟩ mem K
  refine ⟨W, used, R.congr mem K (by decide), seed, cursor, bound, ?_, by rw [mem]; exact O,
    K.2.1.trans rd, K.2.2.trans wr⟩
  rcases result with failed | rejected | ⟨params, status, expected, bytes⟩
  · exact .inl failed
  · exact .inr (.inl rejected)
  · exact .inr (.inr ⟨params, status, expected, by rw [mem]; exact bytes⟩)
end VG.Proof.Dsa.X86.Generation
