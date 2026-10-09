import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedSignContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedConcreteCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopTiming

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached signer uses the original public signing contract. -/
theorem sign_verified_of_loop (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    (htloop : RelCT isa (PairedRS p 16 (LeakEq p 0) (PositiveIK p 16))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) (PositiveOX p 16)) :
    Verified AArch64.target
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) signStack) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  apply Verified.of_correct (k:=pairedSignK p signStack)
  · intro σ h
    exact selectedSign_correct v hp σ h.1 h.2.1 h.2.2
  · apply sign_ct (keccak:=v) (prims_okWith (keccak:=v)) hp3
    · have hd := (Message.pairedInitialization_dle v p).le
      change 16 * _ ≤ 16
      omega
    · intro σ s h r
      apply signLoop_concrete_ok (prims_okWith (keccak:=v)) hp ?_ h r
      have hd := (Message.cachedCommit_dle v hp).le
      change 16 * _ ≤ 16
      omega
    · exact htloop
  · exact pairedSignK_implies_spec hp3

theorem sign_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) :
    Verified AArch64.target
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) signStack) := by
  apply sign_verified_of_loop v hp
  apply signLoop_tr (prims_okWith (keccak:=v)) hp (by decide)
  · have hd := (Message.cachedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega
  · have hd := (Message.pairedBall_dle v p).le
    change 16 * _ ≤ 16
    omega

end VG.Proof.MlDsa.AArch64.Sign.Cached
