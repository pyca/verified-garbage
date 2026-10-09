import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashNonce
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskPrefixTailTiming

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem hash_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {σ s : State} {t : Nat}
    (h : PositiveICh p S σ t p.k s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.hash p) s
      (fun u => PositiveIC p S σ t u ∧ Mask p σ (t+1) u) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.hash
  refine WP.seq (WP.mono (hashSetup_ok hp3 h) fun a ⟨ha,hn,_⟩ => ?_)
  refine WP.mono (hashReady_phase hp hS ha) fun u ⟨hu,hm⟩ => ⟨hu,?_⟩
  rw [nextPolynomial_of_phase hp ha hn] at hm
  exact hm

theorem commit_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.commit P p) s
      (fun u => PositiveIC p S σ t u ∧ Mask p σ (t+1) u) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  refine WP.seq (WP.mono (masks_ok hP hp h hm) fun a ha => ?_)
  refine WP.seq (WP.mono (positiveRows_ok hp3 ha) fun b hb => ?_)
  refine WP.seq (WP.mono (positivePackRows_ok hP hp3 hb) fun c hc => ?_)
  exact hash_ok hp hP.s64 hc

end VG.Proof.MlDsa.AArch64.Sign.Cached
