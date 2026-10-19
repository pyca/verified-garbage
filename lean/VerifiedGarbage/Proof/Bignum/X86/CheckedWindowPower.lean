module

public import VerifiedGarbage.Impl.Bignum.X86.CrtNarrow
public import VerifiedGarbage.Proof.Bignum.X86.CheckedPrimePower
public import VerifiedGarbage.Proof.Mont.X86.WindowExponentiate

/-! # A total factor exponentiation by fixed windows, for arbitrary secret factors -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Proof.Ecdsa.X86

theorem checkedWindowPower_ok {s : State} {base : Addr} {bytes n tab : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : contextBytes n ≤ bytes)
    (W : WinLay n tab bytes) :
    WP isa (checkedWindowPower n tab) s fun t =>
      Context n (safePrime (wordsVal s.mem base (slot n 0) n)) base bytes t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ wordsVal s.mem base (slot n 8) n %
          safePrime (wordsVal s.mem base (slot n 0) n) ∧
      Outs base (primeSetupRanges n ++ windowRanges n (2 * n) tab) s.mem t.mem ∧
      Keeps powerClob s t := by
  have fit : contextBytes n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold checkedWindowPower
  refine WP.seq (WP.mono (primeMask_ok hs hn hz) fun u ⟨Mask, O, K⟩ => ?_)
  have preserve (i : Nat) (hi : i = 0 ∨ i = 5 ∨ i = 8) :
      wordsVal u.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
    have sep := slot_sep (n := n) (i := i) (j := 7) (by omega)
    have bound := slot_bound (n := n) (i := i) (by omega)
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by unfold stride at sep; omega) (by unfold stride at bound; have := hs.nowrap; omega)
  refine WP.seq (WP.mono (preparePrime_ok (hs.of_keeps K (by decide)) hn hn32 hz (preserve 0 (.inl rfl))
    (decide (1 < wordsVal s.mem base (slot n 0) n ∧ wordsVal s.mem base (slot n 0) n % 2 = 1))
    (by simpa only [mask32, decide_eq_true_eq] using Mask) (fun H => of_decide_eq_true H))
    fun v ⟨C, One, R, Ov, Kv⟩ => ?_)
  have Base : wordsVal v.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32 v.mem, primeSetup_value Ov (.inl rfl) (Nat.le_refl _) fit,
      ← wordsVal_eq_val32, preserve 5 (.inr (.inl rfl))]
  have Exponent : val32 v.mem base (slot n 8) (2 * n) = wordsVal s.mem base (slot n 8) n := by
    rw [primeSetup_value Ov (.inr (.inr rfl)) (Nat.le_refl _) fit, ← wordsVal_eq_val32,
      preserve 8 (.inr (.inr rfl))]
  refine WP.mono (windowExponentiate_ok C W (by omega) (Nat.le_refl _) (by omega) One R)
    fun t ⟨Ct, Value, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (K.mono (by decide)).trans (Kv.trans Kt)⟩
  · simpa only [decide_eq_true_eq, safePrime] using Ct
  · rw [Value, Base, Exponent]
    simp only [decide_eq_true_eq, safePrime]
  · exact ((Outs.of_outside O (by simp [primeSetupRanges])).trans
      (Ov.mono (by intro r hr; exact List.mem_append_left _ hr))).trans
      (Ot.mono (by intro r hr; exact List.mem_append_right _ hr))

end VG.Proof.Bignum.X86
