module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCTData
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCTData
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time composition of the complete blinded primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

private def loopInv (len drawBytes n : Nat) : State → State → Prop :=
  Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopBefore len drawBytes p s

section
variable (M : Mont) (K : Kernel) (len drawBytes : Nat)
variable {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
variable (ht₁ : (taint.check (Taint.ofRegs [.x0])
  (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
variable (ht₂ : (taint.check (Taint.ofRegs [.x1])
  (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc₂).isSome = true)

include ht₁ ht₂

private theorem loop_step (n : Nat) :
    RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.AArch64.Generation.primeIteration
        (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes))
      (fun s t => isa.eval (.zero .x .x3) s = isa.eval (.zero .x .x3) t ∧
        (isa.eval (.zero .x .x3) s = some false → True) ∧
        (isa.eval (.zero .x .x3) s = some true → ∃ m < n, loopInv len drawBytes m s t)) := by
  have hw : RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.AArch64.Generation.primeIteration
        (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes))
      (Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopAfter len drawBytes p s) :=
    two_post (two_map id (fun _ _ h => h.2.iteration) (primeIteration_ct M K len drawBytes ht₁ ht₂))
      (fun _ _ h => WP.mono (primeIteration_transition M K h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hw.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have hg : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have hnext := hs.2 hg
  obtain ⟨s₀, res, hstate⟩ := hnext.1
  have hroom : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := hstate.usedBound
  have hdraw := p.draw.prime.drawMin
  refine ⟨p.draw.prime.rand.length - (p.draw.used + p.draw.prime.drawBytes), by omega,
    p.next, ⟨rfl, hnext⟩, ⟨rfl, ht.2 hg⟩, hsp⟩

theorem primeLoop_ct : RelCT isa (Two (LoopBefore len drawBytes))
    (.loop (Impl.Dsa.AArch64.Generation.primeIteration
      (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes)) (.zero .x .x3)) (fun _ _ => True) := by
  rintro s t tr₁ tr₂ u v ⟨p, hs, ht, hsp⟩ e₁ e₂
  exact RelCT.loop (loopInv len drawBytes) (loop_step M K len drawBytes ht₁ ht₂)
    (p.draw.prime.rand.length - p.draw.used) s t tr₁ tr₂ u v ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ e₁ e₂

theorem millerRabin_ct :
    RelCT isa (Two fun p s => DrawBefore len drawBytes p s ∧ p.used ≤ p.prime.rand.length)
      (Impl.Dsa.AArch64.Generation.millerRabin M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.millerRabin
  refine RelCT.seq (two_post (Ψ := fun p s => LoopBefore len drawBytes ⟨p, 1, 0⟩ s)
    (two_taint [.x0] ?_ (by taint_decide)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hs := hs.1.1
    have ht := ht.1.1
    exact hs.ready.ws.x0.trans ht.ready.ws.x0.symm
  · intro p s h
    have hs := h.1.1
    exact WP.mono (primeLoopInit_ok hs h.2) fun _ ht =>
      ⟨⟨s, primeRest p.prime 1 0 p.used, ht⟩, h.1.2⟩
  · exact two_map (fun p : DrawPublic => (⟨p, 1, 0⟩ : PrimeIterationPublic))
      (fun _ _ h => h) (primeLoop_ct M K len drawBytes ht₁ ht₂)

end
end VG.Proof.Dsa.AArch64.Generation
