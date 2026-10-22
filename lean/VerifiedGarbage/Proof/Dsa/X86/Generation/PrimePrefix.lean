module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTransfer
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorAt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparationFrame

/-! Prepare all mathematical candidate data before installing the compact header. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem prime_prefix {s : State} {base : Addr} {bytes n candidate bits : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - BitVec.ofNat 32 16) base bytes)
    (lower : 4 ≤ n) (upper : n ≤ 48)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 3 ≤ candidate)
    (odd : candidate % 2 = 1) (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n)
    (top : 2 ^ (bits - 1) ≤ candidate) :
    WP isa (primePrefix n bits) s fun t =>
      PrimeContext base n candidate t ∧
      val32 t.mem (off base Layout.arithmetic) 160 (2 * n) = Spec.MillerRabin.exponent candidate ∧
      (word t.mem (off base Layout.arithmetic) 64).toNat = 2 ^ (VG.Proof.RsaKeyGen.mrA candidate % 64) ∧
      PreparationFrame base (s.gpr .esp) s t ∧ Keeps powerClob s t := by
  have parentCapacity : montgomeryBytes ≤ bytes := by unfold montgomeryBytes; omega
  unfold primePrefix
  refine WP.seq (WP.mono (parent_constants scr parentCapacity room (by omega) upper modulus (by omega)
    odd bitsLow bitsHigh top) fun a ⟨Ca, ordinary, square, one, minus, Fa, Ka⟩ => ?_)
  have SA := scr.of_keeps Ka (by decide)
  have PA : PrimeContext base n candidate a := ⟨Ca, ordinary, square, one, minus⟩
  refine WP.seq (WP.mono (candidate_transfer SA capacity Ca upper)
    fun b ⟨Cb, candidateB, values, Fb, Kb⟩ => ?_)
  have PB : PrimeContext base n candidate b := ⟨Cb,
    (values 3 (by decide)).trans PA.ordinary, (values 4 (by decide)).trans PA.square,
    (values 6 (by decide)).trans PA.one, (values 7 (by decide)).trans PA.minus⟩
  have Kpre : Keeps powerClob s b := Ka.trans (Kb.mono (by simp [powerClob]))
  have SB := scr.of_keeps Kpre (by decide)
  have roomB : CallRoom (b.gpr .esp) base bytes := by rw [Kpre.1 .esp (by decide)]; exact room
  have stackB : StkOk (b.gpr .esp - BitVec.ofNat 32 16) base bytes := by
    rw [Kpre.1 .esp (by decide)]; exact stack
  refine WP.mono (factor_at SB capacity roomB stackB lower upper candidateB large odd)
    fun t ⟨exponent, tail, Ft, Kt⟩ => ?_
  have PT : PrimeContext base n candidate t := PB.frame_keep Kt (by decide) (by decide) Ft (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact parent_arithmetic_apart base (Nat.le_refl _)
    · rw [List.mem_singleton.mp hr]; exact parent_stack_apart roomB parentCapacity)
  have FF := preparation_factor_frame Ft roomB.low
  rw [Kpre.1 .esp (by decide)] at FF
  exact ⟨PT, exponent, tail, Frame.trans
    (Frame.trans (preparation_montgomery_frame Fa upper) (preparation_candidate_frame Fb upper)) FF,
    Kpre.trans (Kt.mono (by intro r hr; cases r <;> simp_all [powerClob]))⟩

end VG.Proof.Dsa.X86.Generation
