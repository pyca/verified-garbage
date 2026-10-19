module

public import VerifiedGarbage.Proof.Bignum.X86.CrtFactorFrame
public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowPower

/-! # Both CRT factor residues are saved while all imported components remain available -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

def powersRanges (n : Nat) : List (Nat × Nat) :=
  arithmeticRanges n ++ [(slot n mpSlot, 16 * n), (slot n mqSlot, 16 * n), tableRange n]

/-- What the factors' exponentiations at `half n` words need: each factor's
length (a public argument) and, when it fits `half n` words, the factor and
its exponent below `2 ^ (64 half n)`. -/
structure PowerArgs (base : Addr) (bytes n : Nat) (s : State) : Prop where
  pLen : ∃ v, CallArgument s base bytes 7 v ∧ (v.toNat ≤ 8 * half n →
    wordsVal s.mem base (slot n pSlot) n < 2 ^ (64 * half n) ∧
      wordsVal s.mem base (slot n dpSlot) n < 2 ^ (64 * half n))
  qLen : ∃ v, CallArgument s base bytes 9 v ∧ (v.toNat ≤ 8 * half n →
    wordsVal s.mem base (slot n qSlot) n < 2 ^ (64 * half n) ∧
      wordsVal s.mem base (slot n dqSlot) n < 2 ^ (64 * half n))

theorem PowerArgs.keep {base : Addr} {bytes n : Nat} {s t : State} (h : PowerArgs base bytes n s)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem)
    (P : wordsVal t.mem base (slot n pSlot) n = wordsVal s.mem base (slot n pSlot) n)
    (DP : wordsVal t.mem base (slot n dpSlot) n = wordsVal s.mem base (slot n dpSlot) n)
    (Q : wordsVal t.mem base (slot n qSlot) n = wordsVal s.mem base (slot n qSlot) n)
    (DQ : wordsVal t.mem base (slot n dqSlot) n = wordsVal s.mem base (slot n dqSlot) n) :
    PowerArgs base bytes n t := by
  obtain ⟨vp, AP, BP⟩ := h.pLen
  obtain ⟨vq, AQ, BQ⟩ := h.qLen
  exact ⟨⟨vp, AP.keep K sp O, by rw [P, DP]; exact BP⟩, ⟨vq, AQ.keep K sp O, by rw [Q, DQ]; exact BQ⟩⟩

theorem powers_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (args : PowerArgs base bytes n s) :
    WP isa (powers n) s fun t =>
      let xp := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dpSlot) n %
        safePrime (wordsVal s.mem base (slot n pSlot) n)
      let xq := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dqSlot) n %
        safePrime (wordsVal s.mem base (slot n qSlot) n)
      wordsVal t.mem base (slot n mpSlot) n = xp ∧ wordsVal t.mem base (slot n mpSlot) (2 * n) = xp ∧
      wordsVal t.mem base (slot n mqSlot) n = xq ∧ wordsVal t.mem base (slot n mqSlot) (2 * n) = xq ∧
      Outs base (powersRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  obtain ⟨vp, AP, BP⟩ := args.pLen
  obtain ⟨vq, AQ, BQ⟩ := args.qLen
  unfold powers
  refine WP.seq (WP.mono (factorPowerFit_ok hs hn hn32 hz (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) AP) fun u ⟨PV, O, K⟩ => ?_)
  obtain ⟨P, Pw⟩ := PV BP
  have AQ' := AQ.keep K (by decide) (factor_outside O (by decide) hz)
  have qKeep := factor_value O (i := qSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have dqKeep := factor_value O (i := dqSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  refine WP.mono (factorPowerFit_ok (hs.of_keeps K (by decide)) hn hn32 hz
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) AQ') fun t ⟨QV, Ot, Kt⟩ => ?_
  obtain ⟨Q, Qw⟩ := QV (by rw [qKeep, dqKeep]; exact BQ)
  have Input := factor_value O (i := inputSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have Exponent := factor_value O (i := dqSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have Prime := factor_value O (i := qSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  refine ⟨?_, ?_, ?_, ?_, ?_, K.trans Kt⟩
  · rw [factor_value Ot (by decide) (by decide) (by decide) (by omega) fit, P]
  · rw [factor_value Ot (by decide) (by decide) (by decide) (by omega) fit, Pw]
  · rw [Q, Input, Exponent, Prime]
  · rw [Qw, Input, Exponent, Prime]
  · have first : Outs base (powersRanges n) s.mem u.mem := O.mono (by
      intro r hr
      simp only [factorRanges, powersRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h)))
    exact first.trans (Ot.mono (by
      intro r hr
      simp only [factorRanges, powersRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))))

end VG.Proof.Bignum.X86.Crt
