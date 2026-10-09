import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopConcrete
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedDepth

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedSign_correct (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) (σ : State)
    (hpre : (signK p 16).pre σ) (hr : StaticRoots 16 σ) (rp : PairedRoots 16 σ) :
    ∃t s',Exec isa (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) σ t s' ∧
      abiPreserved σ s' ∧ (signK p 16).post σ s' := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  apply sign_correct (keccak:=v) (prims_okWith (keccak:=v)) hp3 σ hpre hr rp
  · have hd := (Message.pairedInitialization_dle v p).le
    change 16 * _ ≤ 16
    omega
  · intro σ s h r
    apply signLoop_concrete_ok (prims_okWith (keccak:=v)) hp ?_ h r
    have hd := (Message.cachedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega

end VG.Proof.MlDsa.AArch64.Sign.Cached
