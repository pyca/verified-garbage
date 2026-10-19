module
public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Bignum.X86.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86.CheckedPrimePower

import VerifiedGarbage.Proof.Bignum.X86.CrtLoadCoefficient
import VerifiedGarbage.Proof.Bignum.X86.CheckedPreparePrime
import VerifiedGarbage.Proof.Bignum.X86.PrimeSetupFrame
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout

/-! # The coefficient stage uses the preserved factor residues and inverse -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

theorem coefficient_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (mp : wordsVal s.mem base (slot n mpSlot) n < safePrime (wordsVal s.mem base (slot n pSlot) n)) :
    WP isa (coefficient n) s fun t =>
      wordsVal t.mem base (slot n 7) n =
        ((wordsVal s.mem base (slot n mpSlot) n + safePrime (wordsVal s.mem base (slot n pSlot) n) -
          wordsVal s.mem base (slot n mqSlot) n % safePrime (wordsVal s.mem base (slot n pSlot) n)) %
          safePrime (wordsVal s.mem base (slot n pSlot) n) * wordsVal s.mem base (slot n inverseSlot) n) %
          safePrime (wordsVal s.mem base (slot n pSlot) n) ∧
      Outs base (arithmeticRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit : contextBytes n ≤ 2 ^ 64 := by have := hs.nowrap; have := context_fits n; omega
  unfold coefficient
  refine WP.seq (WP.mono (loadCoefficient_ok hs hn hz) fun u ⟨P, Q, Mp, QI, O, K⟩ => ?_)
  refine WP.seq (WP.mono (checkedPreparePrime_ok (hs.of_keeps K (by decide)) hn hn32
    (Nat.le_trans (context_fits n) hz)) fun v ⟨C, One, R, Ov, Kv⟩ => ?_)
  have preserve (i : Nat) (hi : i = 5 ∨ i = 6 ∨ i = 8) :
      wordsVal v.mem base (slot n i) n = wordsVal u.mem base (slot n i) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact primeSetup_value Ov hi (by omega) fit
  refine WP.mono (crtCoefficient_ok C (by rw [preserve 6 (.inr (.inl rfl)), Mp, P]; exact mp) One R)
    fun t ⟨_, V, Ot, Kt⟩ => ?_
  refine ⟨?_, (O.trans ?_).trans (coefficient_arithmetic_frame Ot),
    ((K.mono (by decide)).trans Kv).trans (Kt.mono (by decide))⟩
  · rw [V, preserve 6 (.inr (.inl rfl)), preserve 5 (.inl rfl), preserve 8 (.inr (.inr rfl)), Mp, Q, QI, P]
  · apply prime_arithmetic_frame
    exact Ov.mono (by intro r hr; exact List.mem_append_left _ hr)

end VG.Proof.Bignum.X86.Crt
