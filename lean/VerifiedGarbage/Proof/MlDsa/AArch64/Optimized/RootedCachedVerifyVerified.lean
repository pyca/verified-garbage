import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifySat

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts)

/-- Cached-key message verification with both immutable transform tables,
original public leakage, and the unchanged cached-digest semantics. -/
theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} {n : String} {c : Prog isa}
    (hV : Message.OptimizedVerify.VerifyFn p c) (hp : p ∈ params) :
    Verified AArch64.target (verifyMessageCached v.callee n c p)
      (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16) := by
  refine ⟨fun _ h=>let ⟨tr,t,he,ha,hq⟩:=verifyMessageCached_wp v hV hp h;⟨tr,t,he,ha,hq⟩,
    verifyMessage_ct v hV hp,verifySat p,verify_sat ?_⟩
  simpa only [Sign.Ok3,params,List.mem_cons,List.not_mem_nil,or_false] using hp

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
