module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT

/-! # Timing of the complete native DSA seed attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

def SeedAttemptBefore (n pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore n qLen p s ∧ p.context.geo.pLen = pLen

theorem seedAttempt_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedAttemptBefore n pLen qLen))
      (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen) (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold seedAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T n hn qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter n pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2) (seedPrimeFinish_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
