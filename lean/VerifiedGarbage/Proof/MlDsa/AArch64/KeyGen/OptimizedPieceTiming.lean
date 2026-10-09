import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64
open VG.Spec.MlDsa (Params)

/-- Ordinary key-generation pieces preserve the immutable root tables through
 their already-proved write footprint and the bounded call stack. -/
theorem piece_rooted {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : Piece p S I J c) (hd : 16*c.aarch64Depth≤S) (hS : S<2^64) :
    RelCT isa (RootPair p S I) c (RootPair p S J) := by
  apply rootPair_progress
  · intro σ s hp hi roots
    exact roots.phase hd hS (h.ok σ s hp hi)
  · apply RelCT.mono h.tr
    · rintro x y ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,_⟩
      exact ⟨σ,τ,hσ,hτ,pub,hx.1,hy.1⟩
    · intro _ _ _
      trivial

theorem rootPair_mono {p : Params} {S : Nat} {I J : State→State→Prop}
    (h : ∀σ s,I σ s→J σ s) {x y : State} (hr : RootPair p S I x y) : RootPair p S J x y := by
  obtain ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,et⟩ := hr
  exact ⟨⟨σ,τ,hσ,hτ,pub,⟨h _ _ hx.1,hx.2⟩,⟨h _ _ hy.1,hy.2⟩⟩,et⟩

theorem rootPair_finish {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (hw : ∀σ s,kgPre p S σ→I σ s→Sign.StaticRoots S s→WP isa c s (J σ))
    (ht : RelCT isa (RootPair p S I) c fun _ _ => True) :
    RelCT isa (RootPair p S I) c (R p S J) := by
  intro x y tx ty u v hr ex ey
  obtain ⟨he,_⟩ := ht _ _ _ _ _ _ hr ex ey
  obtain ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,_⟩ := hr
  obtain ⟨_,u',eu,ju⟩ := hw σ x hσ ix.1 ix.2
  obtain ⟨_,v',ev,jv⟩ := hw τ y hτ iy.1 iy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨he,σ,τ,hσ,hτ,pub,ju,jv⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
