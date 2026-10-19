module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.IterationPublic
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public transitions of the finite DSA witness loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

def PrimeIterationPublic.next (p : PrimeIterationPublic) : PrimeIterationPublic :=
  ⟨⟨p.draw.prime, p.draw.used + p.draw.prime.drawBytes⟩, p.i + 1, p.nextUniform⟩

def LoopBefore (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  (∃ s₀ res, PrimeLoopState p.draw.prime s₀ res p.i p.uni p.draw.used s) ∧
    p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

theorem LoopBefore.iteration {len drawBytes : Nat} {p : PrimeIterationPublic} {s : State}
    (h : LoopBefore len drawBytes p s) : IterationBefore len drawBytes p s := by
  obtain ⟨s₀, res, hs⟩ := h.1
  exact ⟨⟨hs.state, h.2⟩, hs.usedBound, hs.ki, hs.kuni, hs.counter_bound⟩

def LoopAfter (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  isa.eval (.zero .x .x3) s = some p.continues ∧ (p.continues = true → LoopBefore len drawBytes p.next s)

theorem primeIteration_transition (M : Mont) (K : Kernel) {len drawBytes : Nat}
    {p : PrimeIterationPublic} {s : State} (h : LoopBefore len drawBytes p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeIteration
      (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes)) s (LoopAfter len drawBytes p) := by
  obtain ⟨s₀, res, hs⟩ := h.1
  have hw := wp_and (primeIteration_ok M K hs) (iteration_public M K hs)
  rw [h.2.1, h.2.2] at hw
  refine WP.mono hw fun t ⟨ht, hz, huni⟩ => ⟨hz, fun hgo => ?_⟩
  rcases ht with ⟨he, _⟩ | ⟨_, uni', hn⟩
  · rw [hz, hgo] at he
    cases he
  · have heq : BitVec.ofNat 64 uni' = BitVec.ofNat 64 p.nextUniform := hn.kuni.symm.trans (huni hgo)
    have hb : p.witness.2.toNat ≤ 1 := by cases p.witness.2 <;> decide
    have hsmall : p.nextUniform < 2 ^ 64 := by
      unfold PrimeIterationPublic.nextUniform
      have := hs.counter_bound.2
      omega
    have hsmall' : uni' < 2 ^ 64 := by have := hn.counter_bound.2; omega
    have he : uni' = p.nextUniform := by
      have hh := congrArg BitVec.toNat heq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall'] using hh
    subst uni'
    exact ⟨⟨s₀, res, by simpa only [PrimeIterationPublic.next, h.2.2] using hn⟩, h.2⟩

end VG.Proof.Dsa.AArch64.Generation
