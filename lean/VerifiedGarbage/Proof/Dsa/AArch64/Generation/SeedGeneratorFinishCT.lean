module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT

/-! # Complete generator search, phase gate, packing, and validation timing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem seedGeneratorFinish_ct (M : Mont)  (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore pLen qLen))
      (.seq (generatorSearch M.mm pLen) (onSuccess (finishDomain M.mm pLen qLen)))
      (fun _ _ => True) := by
  have width : pLen = 128 ∨ pLen = 256 ∨ pLen = 384 := by
    rcases sizes with h | h | h <;> simp [h.1]
  refine RelCT.seq (two_post (seedGenerator_ct M pLen qLen width)
    (fun _ _ h => seedGenerator_after M h)) ?_
  apply onSuccess_ct (Φ := SeedGeneratorAfter pLen qLen) (fun p : SeedGeneratorPublic => p.seed.context) SeedGeneratorPublic.status
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedGeneratorAfter_congr h hm hk)
  exact two_map SeedGeneratorPublic.finish (fun _ _ h => h.1.2 h.2) (finishDomain_ct M pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation
