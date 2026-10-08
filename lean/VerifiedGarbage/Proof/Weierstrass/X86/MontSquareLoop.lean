import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRound
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic

/-! # Eight REDC rounds after full-width x86 P-256 squaring -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

def SquareInv (base : Addr) (T i : Nat) (mem : Mem) : Prop :=
  val32 mem base (own 4 + 4 * i) (17 - i) < 2 ^ (32 * (16 - i)) + p256Prime ∧
  ∃ U, U < 2 ^ (32 * i) ∧
    2 ^ (32 * i) * val32 mem base (own 4 + 4 * i) (17 - i) = T + U * p256Prime

theorem squareRounds_ok {s : State} {base : Addr} {T : Nat} (hb : Bx s base 8192)
    (hI : SquareInv base T 0 s.mem) : ∀ r, r ≤ 8 →
    WP isa (.block (squareRounds r)) s fun u =>
      Outside base (own 4) 68 s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧ SquareInv base T r u.mem
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, hI⟩
  | r + 1, hr => by
    rw [squareRounds]
    refine WP.block_append (WP.mono (squareRounds_ok hb hI r (by omega)) fun t ⟨O, K, H, U, hU, E⟩ => ?_)
    have hbt := hb.of_keeps K (by decide)
    refine WP.mono (squareRound_ok hbt (by omega) (square_round_room (by omega) H))
      fun u ⟨O', K', q, hq, E'⟩ => ⟨O.trans O', K.trans K', ?_, ?_⟩
    · have h := square_round_bound (by omega : r < 8) hq H E'
      rwa [show 17 - (r + 1) = 16 - r by omega]
    · have h := square_round_multiple hq hU E E'
      rwa [show 17 - (r + 1) = 16 - r by omega]

/-- The final nine words are below `2p` and congruent to the square times `R⁻¹`. -/
theorem squareReduce_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (ha : a < p256Prime) (hT : val32 s.mem base (own 4) 17 = a * a) :
    WP isa (.block (squareRounds 8)) s fun u =>
      Outside base (own 4) 68 s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧
      val32 u.mem base (own 4 + 32) 9 < 2 * p256Prime ∧
      ∃ U, 2 ^ 256 * val32 u.mem base (own 4 + 32) 9 = a * a + U * p256Prime := by
  have hp : p256Prime < 2 ^ 256 := by decide
  have haa := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_trans ha hp) (Nat.lt_trans ha hp)
  have hI : SquareInv base (a * a) 0 s.mem := by
    simp only [SquareInv, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.one_mul, hT]
    refine ⟨?_, 0, by decide, by simp⟩
    omega
  refine WP.mono (squareRounds_ok hb hI 8 (by decide)) fun u ⟨O, K, _, U, hU, E⟩ =>
    ⟨O, K, square_final_bound ha hU E, U, E⟩

end VG.Proof.Weierstrass.X86.Mont
