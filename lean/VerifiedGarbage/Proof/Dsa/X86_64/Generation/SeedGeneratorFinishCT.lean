module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorCT

/-! # Complete generator search, phase gate, packing, and validation timing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem seedGeneratorFinish_ct (M : Mont) (Sq : MontS) (n pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen))
      (.seq (generatorSearch Sq.mm M.mm pLen) (onSuccess (finishDomain Sq.mm M.mm pLen qLen)))
      (fun _ _ => True) := by
  have width : pLen = 128 ∨ pLen = 256 ∨ pLen = 384 := by
    rcases sizes with h | h | h <;> simp [h.1]
  refine RelCT.seq (two_post (seedGenerator_ct M Sq n pLen qLen width)
    (fun _ _ h => seedGenerator_after M Sq h)) ?_
  apply onSuccess_ct (Φ := SeedGeneratorAfter pLen qLen) (fun p : SeedGeneratorPublic => p.seed.context) SeedGeneratorPublic.status
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedGeneratorAfter_congr h hm hk)
  exact two_map SeedGeneratorPublic.finish (fun _ _ h => h.1.2 h.2) (finishDomain_ct M Sq pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
