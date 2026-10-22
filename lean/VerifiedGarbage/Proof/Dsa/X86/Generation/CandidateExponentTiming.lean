module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateExponentStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentTiming
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticTimingState
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! Complete candidate exponent preparation composes the shared arithmetic timing proofs. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Impl.Dsa.X86.Generation (arithmeticLay)

private theorem certificate : ∃ hc,
    (VG.Taint.check taint arithmeticTaint
      (Impl.Dsa.X86.Generation.candidateExponentStart arithmeticLay) hc).isSome = true :=
  ⟨_, by taint_decide⟩

private theorem prefix_public {s : State} {base : Addr} {bytes len count : Nat} {sp : BitVec 32}
    {args : Nat → Byte} (ws : RtWs arithmeticLay s base bytes len count)
    (A : ArithmeticFrame sp args s) (arrays : 3 ≤ count) :
    WP isa (Impl.Dsa.X86.Generation.candidateExponentStart arithmeticLay) s fun t =>
      RtWs arithmeticLay t base bytes len count ∧ ArithmeticFrame sp args t := by
  refine WP.mono (candidate_exponent_start ws arrays rfl) ?_
  rintro t ⟨ht, F, _, _, K⟩
  exact ⟨ht, A.after_key ws K (by decide) F
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> omega) (by simp)⟩

private theorem prefix_ct {base : Addr} {bytes len count : Nat} {sp : BitVec 32} {args : Nat → Byte}
    (arrays : 3 ≤ count) :
    RelCT isa (ArithmeticPair base bytes len count sp args)
      (Impl.Dsa.X86.Generation.candidateExponentStart arithmeticLay)
      (ArithmeticPair base bytes len count sp args) := by
  obtain ⟨hc, checked⟩ := certificate
  have trace := RelCT.taint (A := taint) arithmeticTaint
    (P := ArithmeticPair base bytes len count sp args) (fun _ _ h => h.agree) checked
  have work : ∀ s t, ArithmeticPair base bytes len count sp args s t →
      WP isa (Impl.Dsa.X86.Generation.candidateExponentStart arithmeticLay) s
        (fun u => RtWs arithmeticLay u base bytes len count ∧ ArithmeticFrame sp args u) ∧
      WP isa (Impl.Dsa.X86.Generation.candidateExponentStart arithmeticLay) t
        (fun u => RtWs arithmeticLay u base bytes len count ∧ ArithmeticFrame sp args u) :=
    fun _ _ h => ⟨prefix_public h.1 h.2.2.1 arrays, prefix_public h.2.1 h.2.2.2 arrays⟩
  exact (trace.wp work).mono (fun _ _ h => h)
    (fun _ _ ⟨_, ⟨ws, A⟩, ⟨wt, B⟩⟩ => ⟨ws, wt, A, B⟩)

theorem prepare_candidate_exponent_ct {base : Addr} {bytes len count : Nat} {sp : BitVec 32}
    {args : Nat → Byte} (arrays : 3 ≤ count) (bits : 32 * kw len ≤ 16384) :
    RelCT isa (ArithmeticPair base bytes len count sp args)
      (Impl.Dsa.X86.Generation.prepareCandidateExponent arithmeticLay) (fun _ _ => True) :=
  (prefix_ct arrays).seq ((halving_ct (by omega) bits).seq
    (prepare_exponent_ct.mono (fun _ _ h => h.agree) (fun _ _ _ => trivial)))

end VG.Proof.Dsa.X86.Generation
