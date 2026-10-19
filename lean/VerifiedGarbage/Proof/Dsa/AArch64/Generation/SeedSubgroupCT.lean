module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedCTState

/-! # Compose seed argument setup with the complete subgroup-generation phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem seedArguments_ct (qLen : Nat) (hlen : qLen = 20 ∨ qLen = 32) :
    RelCT isa (Two (SeedBefore qLen)) (.block (seedArguments qLen)) (Two (SeedPrepared qLen)) := by
  rcases hlen with rfl | rfl
  all_goals
    exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
      (fun _ _ h => seedArguments_ready h)

theorem seedSubgroup_ct (H : GenerationHashes) (M : Mont) (K : Kernel)
    (qLen : Nat) (hlen : qLen = 20 ∨ qLen = 32) :
    RelCT isa (Two (SeedBefore qLen))
      (.seq (.block (seedArguments qLen)) (subgroup H.sha1 H.sha256 M.mm K.run qLen)) (fun _ _ => True) :=
  RelCT.seq (seedArguments_ct qLen hlen)
    (two_map SeedPublic.subgroup (fun _ _ h => seedPrepared_subgroup h) (subgroup_ct H M K qLen hlen))

end VG.Proof.Dsa.AArch64.Generation
