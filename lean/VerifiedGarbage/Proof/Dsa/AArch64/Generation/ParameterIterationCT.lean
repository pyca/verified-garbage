module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterTailCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterTailCT

/-! A complete parameter-search iteration has a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.MillerRabin.AArch64

theorem parameterIteration_ct_of (H : GenerationHashes) (M : Mont) (K : Kernel) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (chunkCheck seedTape qLen)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block (tapeTake seedTape qLen)) hc₂).isSome = true) :
    RelCT isa (Two (ParameterBefore pLen qLen))
      (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 M.mm K.run pLen qLen))
      (Two (ParameterIterationAfter pLen qLen)) := by
  unfold tapeIteration
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht₁)
    (fun _ _ h => parameter_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
      (fun _ _ h => parameter_exhausted h.1 h.2)
  · have tail : RelCT isa (Two (ParameterAvailable pLen qLen))
        (.seq (.block (tapeTake seedTape qLen))
          (.seq (seedAttempt H.sha1 H.sha256 M.mm K.run pLen qLen) (.block tapeStatus)))
        (Two (ParameterIterationAfter pLen qLen)) := by
      refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht₂)
        (fun _ _ h => parameter_take h))
        (RelCT.seq (two_post (parameter_body_ct H M K pLen qLen sizes)
          (fun _ _ h => parameter_body_ready H M K h)) ?_)
      exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
        (fun _ _ h => parameter_status h)
    exact two_map (fun p : ParameterPublic => p)
      (fun _ _ h => parameter_available h.1 h.2) tail

theorem parameterIteration_ct (H : GenerationHashes) (M : Mont) (K : Kernel) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterBefore pLen qLen))
      (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 M.mm K.run pLen qLen))
      (Two (ParameterIterationAfter pLen qLen)) := by
  have width : qLen = 20 ∨ qLen = 32 := by rcases sizes with h | h | h <;> simp [h.2]
  rcases width with rfl | rfl
  all_goals exact parameterIteration_ct_of H M K pLen _ sizes (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
