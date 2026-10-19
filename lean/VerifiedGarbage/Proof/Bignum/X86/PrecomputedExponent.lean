module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponentSafe
public import VerifiedGarbage.Proof.Bignum.X86.PublicExponent
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Safe execution for all packed values, RSA correctness for a valid stored R² -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedExponent_ok {n bytes m : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s) (hone : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 4) n = 1)
    (hr2 : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n < m) :
    WP isa (exponentiate n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n < m ∧
      (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n = 2 ^ (128 * n) % m →
        wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n =
          wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n ^ val32 s.mem base 128 2 % m) ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  obtain ⟨trace, t, E, C, B, O, K⟩ := precomputedExponent_safe h hone hr2
  refine ⟨trace, t, E, C, B, ?_, O, K⟩
  intro good
  exact (VG.Proof.Dsa.X86.wp_result (exponentiate_ok h hone good) E).2.1

end VG.Proof.Bignum.X86.PublicContext
