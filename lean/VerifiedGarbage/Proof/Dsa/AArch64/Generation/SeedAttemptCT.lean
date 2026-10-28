module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPhaseStableCT

/-! # Timing of the complete native DSA seed attempt -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def SeedAttemptBefore (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore qLen p s ∧ p.context.geo.pLen = pLen

theorem seedAttempt_ct (H : GenerationHashes) (G : GeneratorStage)  (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedAttemptBefore pLen qLen))
      (seedAttempt H.sha1 H.sha256 G.run T.run pLen qLen) (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold seedAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2) (seedPrimeFinish_ct H G T pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation
