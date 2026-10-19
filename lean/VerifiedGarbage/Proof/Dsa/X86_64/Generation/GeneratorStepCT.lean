module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorDecisionCT

/-! # Timing of a complete generator attempt, including both retry decisions -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem generatorStep_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorStep Sq.mm M.mm len) (fun _ _ => True) := by
  unfold generatorStep
  refine RelCT.seq (two_post (generatorInputRange_ct len hl)
    (fun _ _ h => generatorInputRange_mask h))
    (RelCT.seq (generatorTest_ct len GeneratorPlan.inputValid) ?_)
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
      (generatorStatus_ct len 3 (Or.inr rfl))
  · have body : RelCT isa (Two (GeneratorBefore len))
        (seqs [generatorEvaluate Sq.mm M.mm len, generatorRangeFromFrame len true,
          .block [.alu .test .rax (.reg .rax)],
          .ite .e (.block (stackStatus 3)) (.block (stackStatus 1))]) (fun _ _ => True) := by
      simp only [seqs]
      refine RelCT.seq (two_post (generatorEvaluate_ct M Sq len hl)
        (fun _ _ h => generatorEvaluate_ready M Sq h))
        (RelCT.seq (two_post (generatorOutputRange_ct len hl)
          (fun _ _ h => generatorOutputRange_mask h))
          (RelCT.seq (generatorTest_ct len GeneratorPlan.outputValid) ?_))
      refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 3 (Or.inr rfl))
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 1 (Or.inl rfl))
    exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1) body

end VG.Proof.Dsa.X86_64.Generation
