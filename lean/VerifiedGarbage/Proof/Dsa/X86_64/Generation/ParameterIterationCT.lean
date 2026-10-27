module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterTailCT
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterTailCT
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of one complete outer seed-loop iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem parameter_before_pins (n pLen qLen : Nat) : Pins (ParameterBefore n pLen qLen) [.rsp] := by
  intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem parameterIteration_ct_of (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rsp]) (.block (chunkCheck seedTape qLen)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rsp]) (.block (tapeTake seedTape qLen)) hc₂).isSome = true) :
    RelCT isa (Two (ParameterBefore n pLen qLen))
      (tapeIteration seedTape qLen (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen))
      (Two (ParameterIterationAfter n pLen qLen)) := by
  unfold tapeIteration
  refine RelCT.seq (two_piece [.rsp] (parameter_before_pins n pLen qLen) ht₁
    (fun _ _ h => parameter_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => parameter_exhausted h.1 h.2)
    intro p s t hs ht r hr
    exact parameter_before_pins n pLen qLen p s t hs.1.1 ht.1.1 r hr
  · have tail : RelCT isa (Two (ParameterAvailable n pLen qLen))
        (.seq (.block (tapeTake seedTape qLen))
          (.seq (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen) (.block tapeStatus)))
        (Two (ParameterIterationAfter n pLen qLen)) := by
      refine RelCT.seq (two_piece [.rsp] ?_ ht₂ (fun _ _ h => parameter_take h))
        (RelCT.seq (two_post (parameter_body_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes)
          (fun _ _ h => parameter_body_ready (checkName := checkName) H M Sq T h)) ?_)
      · intro p s t hs ht r hr
        exact parameter_before_pins n pLen qLen p s t hs.1 ht.1 r hr
      · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => parameter_status h)
        intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hs.layout.rsp.trans ht.layout.rsp.symm
    exact two_map (fun p : ParameterPublic => p) (fun _ _ h => parameter_available h.1 h.2) tail

theorem parameterIteration_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterBefore n pLen qLen))
      (tapeIteration seedTape qLen (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen))
      (Two (ParameterIterationAfter n pLen qLen)) := by
  have width : qLen = 20 ∨ qLen = 32 := by rcases sizes with h | h | h <;> simp [h.2]
  rcases width with rfl | rfl
  all_goals exact parameterIteration_ct_of (checkName := checkName) H M Sq T n hn pLen _ sizes (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
