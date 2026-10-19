module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeIterationCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
import VerifiedGarbage.Proof.Framework.Omega

/-! # The next primality branch and uniform counter are functions of public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.RsaKeyGen.AArch64

def PrimeIterationPublic.witness (p : PrimeIterationPublic) : Nat × Bool :=
  Spec.RsaKeyGen.witness (p.draw.prime.N - 1)
    (Spec.Rsa.os2ip ((p.draw.prime.rand.drop p.draw.used).take p.draw.prime.drawBytes))

def PrimeIterationPublic.nextUniform (p : PrimeIterationPublic) : Nat := p.uni + p.witness.2.toNat

def PrimeIterationPublic.continues (p : PrimeIterationPublic) : Bool :=
  decide (p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length) &&
    Spec.MillerRabin.round p.draw.prime.N p.witness.1 &&
    decide (p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks)

theorem iteration_public (M : Mont) (K : Kernel) {p : PrimeIterationPublic} 
    {s₀ s : State} {res : Option (Bool × List Byte)}
    (h : PrimeLoopState p.draw.prime s₀ res p.i p.uni p.draw.used s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeIteration
      (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run p.draw.prime.len p.draw.prime.drawBytes)) s
      (fun t => isa.eval (.zero .x .x3) t = some p.continues ∧
        (p.continues = true → word t.mem p.draw.prime.B (8 * kUni) = BitVec.ofNat 64 p.nextUniform)) := by
  unfold Impl.Dsa.AArch64.Generation.primeIteration
  simp only [seqs]
  refine WP.seq (WP.mono (tapeCheck_ok h.state h.usedBound) fun u ⟨hcf, hm, ku⟩ => ?_)
  have hu := h.of_mem hm (ku.mono (by decide))
  refine WP.seq (WP.ite (decide (p.draw.prime.rand.length < p.draw.used + p.draw.prime.drawBytes))
    hcf (fun hshort => ?_) (fun hroom => ?_))
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
      (if Spec.MillerRabin.round p.draw.prime.N p.witness.1 then
        (if p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks then 4 else 1) else 3) at hstat
    refine WP.mono (statCmp_ok hv.ready.ws
      (by split <;> (try split) <;> decide) hstat) fun t ⟨hz, hmem, _⟩ => ?_
    constructor
    · by_cases hp : Spec.MillerRabin.round p.draw.prime.N p.witness.1 = true <;>
        by_cases hg : p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks <;>
        simpa [PrimeIterationPublic.continues, hr, hp, hg] using hz
    · intro hg
      have hp : Spec.MillerRabin.round p.draw.prime.N p.witness.1 = true := by
        have hh := hg
        simp only [PrimeIterationPublic.continues, Bool.and_eq_true] at hh
        exact hh.1.2
      rw [hmem]
      exact (hcount hp).2

end VG.Proof.Dsa.AArch64.Generation
