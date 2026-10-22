module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePrefix
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SaveExponentReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HeaderAt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FinalizeCandidate

/-! Complete candidate preparation satisfies the existing shared round contract. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem prime_preparation {s : State} {base : Addr} {bytes n candidate bits : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - BitVec.ofNat 32 16) base bytes)
    (lower : 4 ≤ n) (upper : n ≤ 48)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 3 ≤ candidate)
    (odd : candidate % 2 = 1) (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n)
    (top : 2 ^ (bits - 1) ≤ candidate) :
    WP isa (primePreparation n bits) s fun t =>
      SavedContext base n candidate t ∧
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic)
        (Layout.arithmeticBytes / 8) ∧
      Spec.MillerRabin.Prepared Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) ∧
      Spec.Rsa.Mont.wOf t.mem (off base Layout.arithmetic) = n ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 0 = candidate ∧
      PreparationFrame base (s.gpr .esp) s t ∧ Keeps powerClob s t := by
  unfold primePreparation
  simp only [List.foldr]
  refine WP.seq (WP.mono (prime_prefix scr capacity room stack lower upper modulus large odd
    bitsLow bitsHigh top) fun a ⟨Ca, exponent, tail, Fa, Ka⟩ => ?_)
  have SA := scr.of_keeps Ka (by decide)
  refine WP.seq (WP.mono (save_exponent_ready SA capacity Ca upper exponent tail)
    fun b ⟨Cb, Fb, Kb⟩ => ?_)
  have Ksb := Ka.trans (Kb.mono (by decide))
  have SB := scr.of_keeps Ksb (by decide)
  refine WP.seq (WP.mono (header_at SB capacity lower upper) fun c ⟨Lc, Wc, Fc, Kc⟩ => ?_)
  have Cc := Cb.frame_keep Kc (by decide) (by decide) Fc (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact parent_arithmetic_apart base (by decide))
  have Ksc := Ksb.trans (Kc.mono (by decide))
  have SC := scr.of_keeps Ksc (by decide)
  refine WP.seq (WP.mono (compact_ready SC capacity Cc upper Lc Wc)
    fun d ⟨Cd, Ld, Wd, candidateD, witnessD, oneD, minusD, exponentD, tailD, Fd, Kd⟩ => ?_)
  have Ksd := Ksc.trans (Kd.mono (by decide))
  have SD := scr.of_keeps Ksd (by decide)
  refine WP.seq (WP.mono (finalize_candidate SD capacity Cd.parent lower upper large odd Ld Wd
    candidateD witnessD oneD minusD exponentD tailD) fun t ⟨Lt, Pt, Wt, Ft, Kt⟩ => WP.block_nil ?_)
  have Ct := Cd.frame_keep Kt (by decide) (by decide) Ft (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact parent_arithmetic_apart base (by decide))
  have Fab : PreparationFrame base (s.gpr .esp) a b := preparation_parent_frame Fb
  have Fbc : PreparationFrame base (s.gpr .esp) b c := preparation_arithmetic_frame Fc (by decide)
  have Fcd : PreparationFrame base (s.gpr .esp) c d := preparation_arithmetic_frame Fd (Nat.le_refl _)
  have Fdt : PreparationFrame base (s.gpr .esp) d t := preparation_arithmetic_frame Ft (by decide)
  exact ⟨Ct, Lt, Pt, Wt, (compact_frame_number Ft upper (show 0 < 28 by decide)).trans candidateD,
    Frame.trans (Frame.trans (Frame.trans (Frame.trans Fa Fab) Fbc) Fcd) Fdt,
    Ksd.trans (Kt.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
