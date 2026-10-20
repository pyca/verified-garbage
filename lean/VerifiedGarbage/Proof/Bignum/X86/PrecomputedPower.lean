module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedPower
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.X86.PublicSetup
public import VerifiedGarbage.Proof.Bignum.X86.ExponentRanges
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedSetupFrame
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponent
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedSetup
import VerifiedGarbage.Proof.Bignum.X86.PublicPower
import VerifiedGarbage.Proof.Mont.X86.ContextFrame

/-! # Reused precomputation is safe unconditionally and computes RSA when valid -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic

theorem precomputedPower_ok {n bytes m : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes)
    (hv : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (hr : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n < m) :
    WP isa (precomputedPower n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n < m ∧
      (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n = 2 ^ (128 * n) % m →
        wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n = wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n ^ val32 s.mem base 128 2 % m) ∧
      Outs base (setupRanges n ++ exponentRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have bound : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold precomputedPower
  refine WP.seq (WP.mono (precomputedSetup_ok hs hn hz hv hm1 hodd) fun u ⟨C, One, O, K⟩ => ?_)
  have R := precomputedSetup_value O (by decide : 5 < 8) (by decide) bound
  have Op := precomputedSetup_ranges O
  refine WP.mono (precomputedExponent_ok C One (by rw [R]; exact hr)) fun t ⟨Ct, B, V, Ot, Kt⟩ => ?_
  refine ⟨Ct, B, ?_, ?_, K.trans Kt⟩
  · intro good
    rw [V (by rw [R]; exact good), setup_input Op bound, setup_exponent Op]
  · exact (Op.mono (by intros; exact List.mem_append_left _ ‹_›)).trans
      (Ot.mono (by intros; exact List.mem_append_right _ ‹_›))

end VG.Proof.Bignum.X86.PublicContext
