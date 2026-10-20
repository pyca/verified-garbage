module

public import VerifiedGarbage.Impl.Bignum.X86.PrimePower
public import VerifiedGarbage.Proof.Bignum.X86.PreparePrime
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
import VerifiedGarbage.Proof.Bignum.X86.PrimeSetupFrame
import VerifiedGarbage.Proof.Mont.X86.Exponentiate

/-! # The secret factor power is defined even for rejected keys -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem primePower_ok {s : State} {base : Addr} {bytes n m : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32)
    (hz : contextBytes n ≤ bytes) (hm : wordsVal s.mem base (slot n 0) n = m)
    (valid : Bool) (mask : s.gpr .ecx = if valid then BitVec.allOnes 32 else 0)
    (accepted : valid = true → 1 < m ∧ m % 2 = 1) :
    WP isa (primePower n) s fun t =>
      Context n (if valid then m else 3) base bytes t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ wordsVal s.mem base (slot n 8) n % (if valid then m else 3) ∧
      Outs base (primeSetupRanges n ++ exponentRanges n (2 * n)) s.mem t.mem ∧
      Keeps powerClob s t := by
  have fit : contextBytes n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold primePower
  refine WP.seq (WP.mono (preparePrime_ok hs hn hn32 hz hm valid mask accepted)
    fun u ⟨C, One, R, O, K⟩ => ?_)
  have Base : wordsVal u.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact primeSetup_value O (.inl rfl) (Nat.le_refl _) fit
  have Exponent : val32 u.mem base (slot n 8) (2 * n) = wordsVal s.mem base (slot n 8) n := by
    rw [wordsVal_eq_val32]
    exact primeSetup_value O (.inr (.inr rfl)) (Nat.le_refl _) fit
  refine WP.mono (exponentiate_ok C (by omega) (Nat.le_refl _) (by omega) One R)
    fun t ⟨Ct, Value, Ot, Kt⟩ => ?_
  exact ⟨Ct, by rw [Value, Base, Exponent],
    (O.mono (by intro r hr; exact List.mem_append_left _ hr)).trans
      (Ot.mono (by intro r hr; exact List.mem_append_right _ hr)), K.trans Kt⟩

end VG.Proof.Bignum.X86
