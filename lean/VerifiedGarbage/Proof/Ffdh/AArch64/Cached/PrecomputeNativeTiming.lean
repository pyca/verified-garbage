module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeEntryTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeMetadataTiming

/-! The complete native public initializer is constant time with respect to all non-public memory. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64

theorem precomputeNative_ct (M : Mont) : RelCT isa (Two PrecomputeReady) (Precompute.code M.mm) (fun _ _ =>True) := by
 unfold Precompute.code
 refine RelCT.seq (two_post precomputeEntry_ct (fun _ _ h =>precomputeEntry_entered h)) ?_
 refine RelCT.seq (two_post (two_map precomputeDomainPolicy (fun _ _ h =>precomputeEntered_policy h) policyDomain_ct)
  (fun _ _ h =>precomputePolicy_metadata h)) ?_
 exact RelCT.seq (two_post (two_map precomputeMetadata (fun _ _ h =>precomputePolicyDone_metadata h) metadata_ct)
  (fun _ _ h =>precomputeMetadata_arithmetic h))
  (two_map precomputeArithmetic (fun _ _ h =>h) (precomputeArithmetic_ct M))

end VG.Proof.Ffdh.AArch64.Cached
