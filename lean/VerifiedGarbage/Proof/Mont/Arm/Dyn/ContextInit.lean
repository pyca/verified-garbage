module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context

import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: setting up the context

`contextSetup n`, for the odd modulus `m > 1` in slot 0, stores `m'`, one in
slot 6 and `R² mod m` in slot 7 (`contextSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest)

/-- The memory the setup changes. -/
def setupRanges (n : Nat) : List (Nat × Nat) :=
  [(0, 4), (slot n 6, 8 * n), (slot n 7, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

/-- The low digit of a number is its low word's. -/
theorem val32_mod16 (m : Mem) (base : Addr) (d k : Nat) (hk : 0 < k) :
    val32 m base d k % 2 ^ 16 = w32 m base d % 2 ^ 16 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [val32, Nat.add_mod, show 2 ^ 32 * val32 m base (d + 4) k = 2 ^ 16 * (2 ^ 16 * val32 m base (d + 4) k) by
    rw [← Nat.mul_assoc], Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]

theorem contextSetup_ok {n size m : Nat} {base : Addr} {s : State} (hs : Ws s base size) (hn : 0 < n)
    (hz : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16) (h128 : 128 * n < 2 ^ 16)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (contextSetup n) s fun t => Context n m base size t ∧ val32 t.mem base (slot n 6) (2 * n) = 1 ∧
      val32 t.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m ∧ Outs base (setupRanges n) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  have nw := hs.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  have low : w32 s.mem base (slot n 0) % 2 ^ 16 = m % 2 ^ 16 := by rw [← hv, val32_mod16 _ _ _ _ (by omega)]
  unfold contextSetup
  refine WP.seq (WP.mono (setupInverse_ok hs (mo := modS n) (by simp only [modS, stride] at *; omega)
    (by simp only [modS, stride] at *; omega) (by omega) (by simp only [modS]; omega)) fun t₁ ⟨w₁, I₁, O₁, R₁, _⟩ => ?_)
  have c₁ : Context n m base size t₁ := by
    refine ⟨w₁, hz, h16, hn, ?_, hm1, ?_⟩
    · rw [O₁.val32 (by simp only [invO]; omega) (by simp only [stride] at *; omega)]; exact hv
    · rw [Nat.add_mod, Nat.mul_mod, ← low, ← Nat.mul_mod, ← Nat.add_mod]; exact I₁
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  refine WP.seq (WP.mono (one_ok w₁ (n := n) (out := oneS n) hn (by simp only [oneS, stride] at *; omega)
    (by simp only [oneS, stride] at *; omega)) fun t₂ ⟨w₂, V₂, O₂, R₂⟩ => ?_)
  have K₂ : OpKeep n base 6 t₁ t₂ := ⟨R₂.mono (by decide), Outs.of_outside O₂ (by simp [oneS])⟩
  have c₂ := c₁.keep (by omega) w₂ K₂
  refine WP.mono (powerTwo_ok c₂ (o := 7) (by decide) (by omega) h128) fun t ⟨c, V, O, R⟩ => ⟨c, ?_, V, ?_, ?_⟩
  · have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega
    rw [slot_val32 O (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw']; exact V₂
  · refine ((Outs.of_outside O₁ (by simp [setupRanges, invO])).trans
      (Outs.of_outside O₂ (by simp [setupRanges, oneS]))).trans (O.mono ?_)
    intro r hr; simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [setupRanges]
  · exact ((R₁.mono (by decide)).trans (R₂.mono (by decide))).trans R

end VG.Proof.Mont.Arm.Dyn
