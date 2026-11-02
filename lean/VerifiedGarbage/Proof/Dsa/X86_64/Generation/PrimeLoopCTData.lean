module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeIterationCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
/-! # Public transitions of the finite DSA witness loop -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/IterationPublic.lean`, which only this module imported.
section

/-! # The next primality branch and uniform counter are functions of public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaKeyGen.X86_64

def PrimeIterationPublic.witness (p : PrimeIterationPublic) : Nat × Bool :=
  Spec.RsaKeyGen.witness (p.draw.prime.N - 1)
    (Spec.Rsa.os2ip ((p.draw.prime.rand.drop p.draw.used).take p.draw.prime.drawBytes))

def PrimeIterationPublic.nextUniform (p : PrimeIterationPublic) : Nat := p.uni + p.witness.2.toNat

def PrimeIterationPublic.continues (p : PrimeIterationPublic) : Bool :=
  decide (p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length) &&
    Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 &&
    decide (p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks)

theorem iteration_public (M : Mont) (K : Kernel) {p : PrimeIterationPublic} {mi : BitVec 64}
    {s₀ s : State} {res : Option (Bool × List Byte)}
    (h : PrimeLoopState p.draw.prime mi s₀ res p.i p.uni p.draw.used s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) s
      (fun t => isa.eval .e t = some p.continues ∧
        (p.continues = true → word t.mem p.draw.prime.B (8 * kUni) = BitVec.ofNat 64 p.nextUniform)) := by
  unfold Impl.Dsa.X86_64.Generation.primeIteration
  simp only [seqs]
  refine WP.seq (WP.mono (tapeCheck_ok h.state h.usedBound) fun u ⟨hcf, hm, ku⟩ => ?_)
  have hu := h.of_mem hm (ku.mono (by decide))
  refine WP.seq (WP.ite (decide (p.draw.prime.rand.length < p.draw.used + p.draw.prime.drawBytes))
    (by simp [eval, hcf]) (fun hshort => ?_) (fun hroom => ?_))
  · have hs : ¬ p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
      simpa only [decide_eq_true_eq, Nat.not_le] using hshort
    exact WP.seq_iff.mp (WP.mono (loopExhausted_ok hu (by omega)) fun _ ht => by
      simpa only [PrimeIterationPublic.continues, decide_eq_false hs, Bool.false_and,
        Bool.false_eq_true, false_implies, and_true] using ht.1)
  · have hr : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
      simpa only [decide_eq_false_iff_not, Nat.not_lt] using hroom
    apply WP.seq_iff.mp
    refine WP.seq (WP.mono (drawRound_ok M K hu.state hr hu.ki hu.kuni
      hu.counter_bound.1 hu.counter_bound.2) fun v ⟨hv, hstat, hcount, _, _⟩ => ?_)
    change word v.mem p.draw.prime.B (8 * kStat) = BitVec.ofNat 64
      (if Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 then
        (if p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks then 4 else 1) else 3) at hstat
    refine WP.mono (statCmp_ok hv.ready.good p.draw.prime.dims.z
      (by split <;> (try split) <;> decide) hstat) fun t ⟨hz, hmem, _⟩ => ?_
    constructor
    · by_cases hp : Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 = true <;>
        by_cases hg : p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks <;>
        simp [eval, hz, PrimeIterationPublic.continues, hr, hp, hg]
    · intro hg
      have hp : Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 = true := by
        have hh := hg
        simp only [PrimeIterationPublic.continues, Bool.and_eq_true] at hh
        exact hh.1.2
      rw [hmem]
      exact (hcount hp).2

end VG.Proof.Dsa.X86_64.Generation
end

end

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
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) s (LoopAfter len drawBytes p) := by
  obtain ⟨mi, s₀, res, hs⟩ := h.1
  have hw := (primeIteration_ok M K hs).and (iteration_public M K hs)
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
