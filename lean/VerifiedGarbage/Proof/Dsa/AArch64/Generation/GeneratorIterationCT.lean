module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchTailCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchTailCT

/-! A complete generator-tape iteration has a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem generatorIteration_ct_of (M : Mont) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (chunkCheck generatorTape len)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block (tapeTake generatorTape len)) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  unfold tapeIteration
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht₁)
    (fun _ _ h => generatorSearch_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
      (fun _ _ h => generatorSearch_exhausted h.1 h.2)
  · have tail : RelCT isa (Two (GeneratorSearchAvailable len))
        (.seq (.block (tapeTake generatorTape len))
          (.seq (generatorStep M.mm len) (.block tapeStatus)))
        (Two (GeneratorSearchIterationAfter len)) := by
      refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht₂)
        (fun _ _ h => generatorSearch_take h))
        (RelCT.seq (two_post (generatorSearch_body_ct M len hl)
          (fun _ _ h => generatorSearch_body_ready M h)) ?_)
      exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
        (fun _ _ h => generatorSearch_status h)
    exact two_map (fun p : GeneratorSearchPublic => p)
      (fun _ _ h => generatorSearch_available h.1 h.2) tail

theorem generatorIteration_ct (M : Mont) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  rcases hl with rfl | rfl | rfl
  all_goals exact generatorIteration_ct_of M _ (by omega) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
