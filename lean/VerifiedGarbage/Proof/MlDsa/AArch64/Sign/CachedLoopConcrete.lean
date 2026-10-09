import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCommitmentCorrect

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem commit_correct {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87)
    (hd : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S) :
    CommitCorrect P p S := by
  intro σ s t h roots hm
  exact WP.mono (WP.pairedRoots (commit_ok hP hp h hm) roots hd hP.s64)
    fun u ⟨⟨hu,hm⟩,ru⟩=>⟨hu,ru,hm⟩

theorem signLoop_concrete_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87)
    (hd : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  exact signLoop_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hd) h roots

end VG.Proof.MlDsa.AArch64.Sign.Cached
