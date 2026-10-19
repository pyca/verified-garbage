module

public import VerifiedGarbage.Impl.Bignum.X86.CheckedPreparePrime
public import VerifiedGarbage.Proof.Bignum.X86.CheckedPrimePower

/-! # Secret-factor setup always supplies a usable Montgomery context -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Proof.Ecdsa.X86

theorem checkedPreparePrime_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : contextBytes n ≤ bytes) :
    WP isa (checkedPreparePrime n) s fun t =>
      Context n (safePrime (wordsVal s.mem base (slot n 0) n)) base bytes t ∧
      wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % safePrime (wordsVal s.mem base (slot n 0) n) ∧
      Outs base (primeSetupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold checkedPreparePrime
  refine WP.seq (WP.mono (primeMask_ok hs hn hz) fun u ⟨Mask, O, K⟩ => ?_)
  have sep := slot_le (n := n) (i := 0) (j := 7) (by decide)
  have bound := slot_bound (n := n) (i := 0) (by decide)
  have N : wordsVal u.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by unfold stride at sep; omega) (by unfold stride at bound; have := hs.nowrap; omega)
  refine WP.mono (preparePrime_ok (hs.of_keeps K (by decide)) hn hn32 hz N
    (decide (1 < wordsVal s.mem base (slot n 0) n ∧ wordsVal s.mem base (slot n 0) n % 2 = 1))
    (by simpa only [mask32, decide_eq_true_eq] using Mask) (fun H => of_decide_eq_true H))
    fun t ⟨C, One, R, Ot, Kt⟩ => ?_
  exact ⟨by simpa only [safePrime, decide_eq_true_eq] using C, One,
    by simpa only [safePrime, decide_eq_true_eq] using R,
    (Outs.of_outside O (by simp [primeSetupRanges])).trans Ot, (K.mono (by decide)).trans Kt⟩

end VG.Proof.Bignum.X86
