import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopCorrect

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem Mask.transfer {p : Params} {S : Nat} {σ τ s : State} {t : Nat}
    (hσ : PositiveIK p S σ s) (hτ : PositiveIK p S τ s) (h : Mask p σ t s) : Mask p τ t s := by
  have hr : rppOf p σ=rppOf p τ := hσ.rpp.symm.trans hτ.rpp
  simpa only [Mask,Yv,hr] using h

/-- A cached mask is independent of the existential initial-state witness:
all witnesses of the current key invariant have the same private mask seed. -/
def CacheHeld (p : Params) (S t : Nat) (s : State) : Prop :=
  ∀σ,PositiveIK p S σ s → Mask p σ t s

theorem cacheHeld_of {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hk : PositiveIK p S σ s) (h : Mask p σ t s) : CacheHeld p S t s :=
  fun _ hτ=>h.transfer hk hτ

theorem PositiveLP.key {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveLP p S σ t s) : PositiveIK p S σ s := by
  rcases h with ⟨_,h⟩|⟨_,h⟩ <;> exact h.k

end VG.Proof.MlDsa.AArch64.Sign.Cached
