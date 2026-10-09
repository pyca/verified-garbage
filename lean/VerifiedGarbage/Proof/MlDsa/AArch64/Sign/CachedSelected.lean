import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.CachedVerified

namespace VG.Proof.MlDsa.AArch64.Sign.CachedSelected
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message

/-- Only paired-SHA3 signing uses the cached commitment. Scalar variants
retain their existing implementation; callers use this same selected body. -/
def code (v : Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 then
    Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)
  else
    Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)

theorem verified (v : Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) :
    Verified target (code v p) (signContract p (abi.withConsts pairedSignRootConsts) 16) := by
  unfold code
  split
  · exact Cached.sign_verified v hp
  · apply pairedSign_verified v
    rcases hp with h|h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

theorem message_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (n : String) :
    Verified target (Impl.MlDsa.AArch64.Message.signMessage v.callee n (code v p) p)
      (signMessageContract p (abi.withConsts pairedSignRootConsts) 16) := by
  have hmem : p∈Message.params := by
    simp only [Message.params,List.mem_cons,List.not_mem_nil,or_false]
    rcases hp with h|h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  unfold code
  split
  · exact Message.Cached.signMessage_verified v hp n
  · exact Message.Paired.signMessage_verified v (Message.Paired.signFn v hmem) hmem

end VG.Proof.MlDsa.AArch64.Sign.CachedSelected
