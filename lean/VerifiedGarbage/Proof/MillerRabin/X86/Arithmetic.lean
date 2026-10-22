module

public import VerifiedGarbage.Proof.MillerRabin.X86.WindowInit
public import VerifiedGarbage.Proof.MillerRabin.X86.Words
public import VerifiedGarbage.Proof.MillerRabin.X86.FinalSquares

/-! # Compose the prepared primality round's complete arithmetic -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem arithmetic_ok {σ : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ σ)
    (tail : σ.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ.mem base 256 (2 * w) - 1)).1 % 64)) :
    WP isa arithmetic σ fun t => Stage base bytes w σ t ∧ w32 t.mem base sF = (finalFlag σ base w).toNat := by
  unfold arithmetic
  refine WP.seq (WP.mono (table_start facts h) fun u table => ?_)
  refine WP.seq (WP.mono (table_loop facts table) fun v complete => ?_)
  refine WP.seq (WP.mono (window_init facts complete) fun z run => ?_)
  refine WP.seq (WP.mono (words_loop facts run) fun t done => ?_)
  exact final_squares facts done tail

theorem final_flag_correct {σ : State} {base : Addr} {w b : Nat}
    (width : Spec.Rsa.Mont.wOf σ.mem base = w)
    (prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact σ.mem base)
    (witness : numAt σ.mem base w 5 = b % val32 σ.mem base 256 (2 * w) * 2 ^ (64 * w) %
      val32 σ.mem base 256 (2 * w)) :
    finalFlag σ base w = Spec.MillerRabin.round (val32 σ.mem base 256 (2 * w)) b := by
  unfold Spec.MillerRabin.Prepared at prepared
  rw [width] at prepared
  rcases prepared with ⟨c3, odd, _, _, one, minus, exponent, _⟩
  simp only [Spec.MillerRabin.compact, candidate_value] at c3 odd one minus exponent
  have bound : val32 σ.mem base 256 (2 * w) < 2 ^ (64 * w) := by
    simpa only [show 32 * (2 * w) = 64 * w by omega] using val32_lt σ.mem base 256 (2 * w)
  unfold finalFlag roundRun tablePower
  rw [one, minus, exponent]
  exact VG.Proof.MillerRabin.Math.final_eq odd c3 bound witness rfl rfl

end VG.Proof.MillerRabin.X86
