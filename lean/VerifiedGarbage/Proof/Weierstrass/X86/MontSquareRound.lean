import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed

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
