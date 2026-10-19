module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TrialCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TrialCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetupCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoopCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime

/-! # Timing of the complete DSA probable-prime operation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem primeCall_setup {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) : PrimeSetupBefore p.draw.prime s := by
  obtain ⟨mi, hs⟩ := h.1
  exact ⟨⟨mi, hs.good⟩, hs.n, p.width⟩

theorem primeCall_ready (M : Mont) {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSetup M.mm) s
      (fun t => DrawBefore len drawBytes p.draw t ∧ p.draw.used ≤ p.draw.prime.rand.length) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (primeInputSetup_ok M hs p.width) fun _ ⟨mi', ht, _, _⟩ =>
    ⟨⟨⟨mi', ht⟩, h.2.2.2⟩, h.2.2.1⟩

theorem probablePrime_ct (M : Mont) (K : Kernel) (len drawBytes : Nat)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Impl.Dsa.X86_64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Impl.Dsa.X86_64.Generation.forceWitness len)) hc₂).isSome = true) :
    RelCT isa (Two (PrimeCallBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.probablePrime M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.probablePrime
  refine RelCT.seq (two_post (primeTrial_ct len drawBytes) (fun _ _ h => primeTrial_tested h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun p : PrimeCallPublic => p.draw.prime) (fun _ _ h => primeCall_setup h.1.1)
        (primeSetup_ct M)) (fun _ _ h => primeCall_ready M h.1.1)) ?_
    exact two_map PrimeCallPublic.draw (fun _ _ h => h) (millerRabin_ct M K len drawBytes ht₁ ht₂)
  · exact two_taint [.rdi] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r
      obtain ⟨mi, hs⟩ := hs.1.1.1
      obtain ⟨mi', ht⟩ := ht.1.1.1
      exact hs.good.rdi.trans ht.good.rdi.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
