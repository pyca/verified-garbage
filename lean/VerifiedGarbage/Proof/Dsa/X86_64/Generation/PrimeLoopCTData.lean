module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.IterationPublic
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public transitions of the finite DSA witness loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def PrimeIterationPublic.next (p : PrimeIterationPublic) : PrimeIterationPublic :=
  ⟨⟨p.draw.prime, p.draw.used + p.draw.prime.drawBytes⟩, p.i + 1, p.nextUniform⟩

def LoopBefore (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  (∃ mi s₀ res, PrimeLoopState p.draw.prime mi s₀ res p.i p.uni p.draw.used s) ∧
    p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

theorem LoopBefore.iteration {len drawBytes : Nat} {p : PrimeIterationPublic} {s : State}
    (h : LoopBefore len drawBytes p s) : IterationBefore len drawBytes p s := by
  obtain ⟨mi, s₀, res, hs⟩ := h.1
  exact ⟨⟨⟨mi, hs.state⟩, h.2⟩, hs.usedBound, hs.ki, hs.kuni, hs.counter_bound⟩

def LoopAfter (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  isa.eval .e s = some p.continues ∧ (p.continues = true → LoopBefore len drawBytes p.next s)

theorem primeIteration_transition (M : Mont) (K : Kernel) {len drawBytes : Nat}
    {p : PrimeIterationPublic} {s : State} (h : LoopBefore len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run len drawBytes)) s (LoopAfter len drawBytes p) := by
  obtain ⟨mi, s₀, res, hs⟩ := h.1
  have hw := (primeIteration_ok M K hs).and (iteration_public M K hs)
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
    exact ⟨⟨mi, s₀, res, by simpa only [PrimeIterationPublic.next, h.2.2] using hn⟩, h.2⟩

end VG.Proof.Dsa.X86_64.Generation
