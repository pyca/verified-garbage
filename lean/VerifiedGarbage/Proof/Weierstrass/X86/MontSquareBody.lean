import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareInit

/-! ## `MontSquareRound` -/

section

/-! # A REDC round on a completed x86 P-256 product -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem squareRound_ok {s : State} {base : Addr} (hb : Bx s base 8192)
    {i : Nat} (hi : i < 8)
    (hlt : val32 s.mem base (own 4 + 4 * i) (17 - i) + (2 ^ 32 - 1) * p256Prime < 2 ^ (32 * (17 - i))) :
    WP isa (.block (squareRound i)) s fun u =>
      Outside base (own 4) 68 s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧
      ∃ q, q < 2 ^ 32 ∧
        2 ^ 32 * val32 u.mem base (own 4 + 4 * (i + 1)) (16 - i) =
          val32 s.mem base (own 4 + 4 * i) (17 - i) + q * p256Prime := by
  have hn := hb.nowrap
  have ho : own 4 = 3840 := rfl
  simp only [squareRound, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_bp hb (d := own 4 + 4 * i) (by omega)) fun t R _ => ?_
  have hbt := hb.of_keeps R.keeps (by decide)
  have hq : (t.gpr .ecx).toNat = w32 s.mem base (own 4 + 4 * i) := by rw [R.gpr]
  have hqB := (t.gpr .ecx).isLt
  have hqp : (t.gpr .ecx).toNat * p256Prime ≤ (2 ^ 32 - 1) * p256Prime :=
    Nat.mul_le_mul_right _ (by omega)
  refine WP.mono (squareRed_ok hbt (w := own 4 + 4 * i) (extra := 7 - i) (by omega)
    (by omega) (by rw [R.mem]; exact hq) ?_) fun u ⟨O, V, K⟩ => ?_
  · rw [R.mem, show 10 + (7 - i) = 17 - i by omega]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hqp _) hlt
  · refine ⟨?_, (R.keeps.mono (by decide)).widen K (by decide), (t.gpr .ecx).toNat, hqB, ?_⟩
    · rw [R.mem] at O
      exact O.mono (by omega) (by omega)
    · rw [R.mem, show 10 + (7 - i) = 17 - i by omega] at V
      have he : 17 - i = (16 - i) + 1 := by omega
      rw [he, val32, val32] at V
      have hlow := (u.mem.readW (off base (own 4 + 4 * i)) 32).isLt
      rw [← hq] at V
      have heq : own 4 + 4 * (i + 1) = own 4 + 4 * i + 4 := by omega
      rw [heq, he, val32, ← hq]
      simp only [p256Prime, w32] at V ⊢
      omega_using [V, hlow]

end VG.Proof.Weierstrass.X86.Mont

end

/-! ## `MontSquareLoop` -/

section

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

end

/-! ## `MontSquareBody` -/

section

/-! # The x86 P-256 square before its common final subtraction -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem squareBody_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (hp : Ptr s .esi a) (ha : a + 32 ≤ own 4) (hA : val32 s.mem base a 8 < p256Prime) :
    WP isa (.block squareBody) s fun u =>
      Outside base (own 4) 100 s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own 4 + 32) 9 < 2 * p256Prime ∧
      ∃ U, 2 ^ 256 * val32 u.mem base (own 4 + 32) 9 =
        val32 s.mem base a 8 * val32 s.mem base a 8 + U * p256Prime := by
  unfold squareBody
  refine WP.block_append (WP.mono (squareInit_ok hb hp ha) fun t ⟨O, K, V⟩ => ?_)
  refine WP.mono (squareReduce_ok (hb.of_keeps K (by decide)) hA V) fun u ⟨O', K', H, E⟩ =>
    ⟨O.trans (O'.mono (by omega) (by omega)), K.widen K' (by decide), H, E⟩

end VG.Proof.Weierstrass.X86.Mont

end
