module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorDecisionCT

/-! # Timing of a complete generator attempt, including both retry decisions -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Bignum.AArch64

theorem generatorStep_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorStep M.mm len) (fun _ _ => True) := by
  unfold generatorStep
  refine RelCT.seq (two_post (generatorInputRange_ct len hl)
    (fun _ _ h => generatorInputRange_mask h))
    ?_
  refine two_ite (fun _ _ _ hs ht => (generatorTest_ok hs.2).trans (generatorTest_ok ht.2).symm) ?_ ?_
  · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
      (generatorStatus_ct len 3 (Or.inr rfl))
  · have body : RelCT isa (Two (GeneratorBefore len))
        (seqs [generatorEvaluate M.mm len, generatorRangeFromFrame len true,
          .ite (.zero .x .x3) (.block (stackStatus 3)) (.block (stackStatus 1))]) (fun _ _ => True) := by
      simp only [seqs]
      refine RelCT.seq (two_post (generatorEvaluate_ct M len hl)
        (fun _ _ h => generatorEvaluate_ready M h))
        (RelCT.seq (two_post (generatorOutputRange_ct len hl)
          (fun _ _ h => generatorOutputRange_mask h))
          ?_)
      refine two_ite (fun _ _ _ hs ht => (generatorTest_ok hs.2).trans (generatorTest_ok ht.2).symm) ?_ ?_
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 3 (Or.inr rfl))
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 1 (Or.inl rfl))
    exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1) body

end VG.Proof.Dsa.AArch64.Generation
