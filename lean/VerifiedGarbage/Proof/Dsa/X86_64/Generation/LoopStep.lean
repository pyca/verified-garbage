module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
import VerifiedGarbage.Proof.Framework.Omega

/-! # One guarded iteration of DSA's finite primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

theorem primeIteration_ok (M : Mont) (K : Kernel) {P : PrimeParams} {mi : BitVec 64} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P mi s₀ res i uni used s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run P.len P.drawBytes)) s fun t =>
        (isa.eval .e t = some false ∧ PrimeLoopEnd P mi s₀ res t) ∨
        (isa.eval .e t = some true ∧ ∃ uni', PrimeLoopState P mi s₀ res (i + 1) uni' (used + P.drawBytes) t) := by
  unfold Impl.Dsa.X86_64.Generation.primeIteration
  simp only [seqs]
  refine WP.seq (WP.mono (tapeCheck_ok h.state h.usedBound) fun u ⟨hcf, hm, ku⟩ => ?_)
  have hu := h.of_mem hm (ku.mono (by decide))
  refine WP.seq (WP.ite (decide (P.rand.length < used + P.drawBytes)) (by simp [eval, hcf])
    (fun hshort => ?_) (fun hroom => ?_))
  · exact WP.seq_iff.mp (WP.mono (loopExhausted_ok hu (by simpa only [decide_eq_true_eq] using hshort))
      fun _ ht => Or.inl ht)
  · exact WP.seq_iff.mp (loopRound_ok M K hu (by simpa only [decide_eq_false_iff_not, Nat.not_lt] using hroom))

end VG.Proof.Dsa.X86_64.Generation
