import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyVerified

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Verify.Optimized

/-- The feature-selected raw verifier shared by all public wrappers. -/
def selectedCode (v : Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 then
    Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p
  else Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p

def selectedConsts (v : Proof.Sha3.AArch64.Permutation) : List (String × List (BitVec 64)) :=
  if v.callee.pairedSha3 then Sign.signRootConsts else []

def selectedAbi (v : Proof.Sha3.AArch64.Permutation) : Abi isa :=
  abi.withConsts (selectedConsts v)

theorem selected_verify_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    Verified target (selectedCode v p) (verifyContract p (selectedAbi v) 16) := by
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact Optimized.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) hp
  · exact Verify.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) p hp (Verify.verify_sat p hp)

theorem optimizedVerifyFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    Message.OptimizedVerify.VerifyFn p
      (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) :=
  ⟨Optimized.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) hp,verifyWith_dle v p⟩

theorem selected_message_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (n : String) :
    Verified target (Impl.MlDsa.AArch64.Message.verifyMessage v.callee n (selectedCode v p) p)
      (verifyMessageContract p (selectedAbi v) 16) := by
  have hm : p∈Message.params := by simpa only [Sign.Ok3,Message.params,List.mem_cons,List.not_mem_nil,or_false] using hp
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact Message.OptimizedVerify.verifyMessage_verified v (optimizedVerifyFn v hp) hm
  · exact Message.verifyMessage_verified v (Message.verifyFn v hm) hm

theorem selected_cached_message_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (n : String) :
    Verified target (Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee n (selectedCode v p) p)
      (verifyMessageCachedContract p (selectedAbi v) 16) := by
  have hm : p∈Message.params := by simpa only [Sign.Ok3,Message.params,List.mem_cons,List.not_mem_nil,or_false] using hp
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify.verifyMessage_verified v (optimizedVerifyFn v hp) hm
  · exact VG.Proof.MlDsa.AArch64.Optimized.CachedVerify.verifyMessage_verified v (Message.verifyFn v hm) hm

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
