module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchStateCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeSearchCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashChoice

/-! # The accepted subgroup enters the complete public-trace prime search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem seedPrime_ct (H : GenerationHashes) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) (fun _ _ => True) := by
  have hq : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  exact two_map SeedPublic.search (fun _ _ h => seedPrime_start h)
    (primeSearch_ct H.sha1 H.sha256 T (generationHash qLen) pLen qLen sizes
      (H.streamOK qLen) (H.hash_matches qLen) (H.hash_size qLen)
      (generationHash_seed hq) (H.seed_size hq) (H.hash_width hq))

end VG.Proof.Dsa.AArch64.Generation
