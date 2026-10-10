import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP

/-!
# ECDSA on x86 (32-bit): the point functions' slots

For coordinates of 3 to 6 words, the ladder calls the point functions
(`ladderP_ok`), which also write their slots and own working space (`ptW`):
above every numbered slot (`ladPt`) and below the tables of bits.
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem sl_below_pt (h6 : c.n ≤ 6) {i : Nat} (hi : i < 45) :
    c.sl i + 8 * c.n ≤ Spec.Weierstrass.Point.oAt c.n := by
  have := sl_lt c hi
  rw [sl_eq c 45] at this
  simp only [Spec.Weierstrass.Point.oAt, Spec.Weierstrass.Point.pAt, Spec.Weierstrass.Point.qAt,
    Spec.Weierstrass.Point.aAt, Spec.Weierstrass.Point.b3At, Spec.Weierstrass.Point.ownAt,
    Spec.Weierstrass.Point.elemBytes, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]
  omega

theorem oAt_le (c : Cfg) : Spec.Weierstrass.Point.oAt c.n ≤ 4096 := by
  simp only [Spec.Weierstrass.Point.oAt, Spec.Weierstrass.Point.pAt, Spec.Weierstrass.Point.qAt,
    Spec.Weierstrass.Point.aAt, Spec.Weierstrass.Point.b3At, Spec.Weierstrass.Point.ownAt,
    Spec.Weierstrass.Point.elemBytes, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]
  omega

/-- The ladder's slots are below the point functions'. -/
theorem ladPt (h : 3 ≤ c.n ∧ c.n ≤ 6) : Point.LadPt c.ladderCfg where
  k3 := h.1
  sl := by
    rw [ladSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ],
      i < 45 := by decide
    exact sl_below_pt h.2 (this i hi)
  mo := sl_below_pt h.2 (i := MP) (by decide)

theorem apart_ptW {i : Nat} (hi : i < 45) :
    ∀ w ∈ Point.ptW c.n, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  unfold Point.ptW at hw
  split at hw
  next h => rw [List.mem_singleton.mp hw]; exact Or.inl (sl_below_pt h.2 hi)
  · simp at hw

theorem tbl_apart_ptW (j t : Nat) :
    ∀ w ∈ Point.ptW c.n, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  unfold Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw, bitsAt_eq]; have := oAt_le c; dsimp only; omega
  · simp at hw

theorem fixedOk_ptW : FixedOk c (Point.ptW c.n) := by
  intro w hw
  unfold Point.ptW at hw
  split at hw
  next h =>
    rw [List.mem_singleton.mp hw]
    exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_pt h.2 (i := 12) (by decide)))
  · simp at hw

theorem ptW_le : ∀ w ∈ Point.ptW c.n, w.1 + w.2 ≤ size := by
  intro w hw
  unfold Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]; have := oAt_le c; dsimp only [size]; omega
  · simp at hw

end VG.Proof.Ecdsa.X86
