module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoopCTData
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoopCTData
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time composition of the complete blinded primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

private def loopInv (len drawBytes n : Nat) : State → State → Prop :=
  Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopBefore len drawBytes p s

section
variable (M : Mont) (K : Kernel) (len drawBytes : Nat)

private theorem loop_step (n : Nat) :
    RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.X86_64.Generation.primeIteration
        (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run))
      (fun s t => isa.eval .e s = isa.eval .e t ∧
        (isa.eval .e s = some false → True) ∧
        (isa.eval .e s = some true → ∃ m < n, loopInv len drawBytes m s t)) := by
  have hw : RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.X86_64.Generation.primeIteration
        (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run))
      (Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopAfter len drawBytes p s) :=
    two_post (two_map id (fun _ _ h => h.2.iteration) (primeIteration_ct M K len drawBytes))
      (fun _ _ h => WP.mono (primeIteration_transition M K h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hw.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have hg : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have hnext := hs.2 hg
  obtain ⟨mi, s₀, res, hstate⟩ := hnext.1
  have hroom : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := hstate.usedBound
  have hdraw := p.draw.prime.drawMin
  refine ⟨p.draw.prime.rand.length - (p.draw.used + p.draw.prime.drawBytes), by omega,
    p.next, ⟨rfl, hnext⟩, rfl, ht.2 hg⟩

theorem primeLoop_ct : RelCT isa (Two (LoopBefore len drawBytes))
    (.loop (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) .e) (fun _ _ => True) := by
  rintro s t tr₁ tr₂ u v ⟨p, hs, ht⟩ e₁ e₂
  exact RelCT.loop (loopInv len drawBytes) (loop_step M K len drawBytes)
    (p.draw.prime.rand.length - p.draw.used) s t tr₁ tr₂ u v ⟨p, ⟨rfl, hs⟩, rfl, ht⟩ e₁ e₂

theorem millerRabin_ct :
    RelCT isa (Two fun p s => DrawBefore len drawBytes p s ∧ p.used ≤ p.prime.rand.length)
      (Impl.Dsa.X86_64.Generation.millerRabin M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.millerRabin
  refine RelCT.seq (two_post (Ψ := fun p s => LoopBefore len drawBytes ⟨p, 1, 0⟩ s)
    (two_taint [.rdi] ?_ (by taint_decide)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1.1
    obtain ⟨mi', ht⟩ := ht.1.1
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · intro p s h
    obtain ⟨mi, hs⟩ := h.1.1
    exact WP.mono (primeLoopInit_ok hs h.2) fun _ ht =>
      ⟨⟨mi, s, primeRest p.prime 1 0 p.used, ht⟩, h.1.2⟩
  · exact two_map (fun p : DrawPublic => (⟨p, 1, 0⟩ : PrimeIterationPublic))
      (fun _ _ h => h) (primeLoop_ct M K len drawBytes)

end
end VG.Proof.Dsa.X86_64.Generation
