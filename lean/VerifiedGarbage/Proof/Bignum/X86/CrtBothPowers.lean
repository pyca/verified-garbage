module

public import VerifiedGarbage.Proof.Bignum.X86.CrtFactorFrame

/-! # Both CRT factor residues are saved while all imported components remain available -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

def powersRanges (n : Nat) : List (Nat × Nat) :=
  arithmeticRanges n ++ [(slot n mpSlot, 16 * n), (slot n mqSlot, 16 * n)]

theorem powers_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes) :
    WP isa (powers n) s fun t =>
      let xp := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dpSlot) n %
        safePrime (wordsVal s.mem base (slot n pSlot) n)
      let xq := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dqSlot) n %
        safePrime (wordsVal s.mem base (slot n qSlot) n)
      wordsVal t.mem base (slot n mpSlot) n = xp ∧ wordsVal t.mem base (slot n mpSlot) (2 * n) = xp ∧
      wordsVal t.mem base (slot n mqSlot) n = xq ∧ wordsVal t.mem base (slot n mqSlot) (2 * n) = xq ∧
      Outs base (powersRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold powers
  refine WP.seq (WP.mono (factorPower_ok hs hn hn32 hz (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨P, Pw, O, K⟩ => ?_)
  refine WP.mono (factorPower_ok (hs.of_keeps K (by decide)) hn hn32 hz
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨Q, Qw, Ot, Kt⟩ => ?_
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
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact first.trans (Ot.mono (by
      intro r hr
      simp only [factorRanges, powersRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inr h))))

end VG.Proof.Bignum.X86.Crt
