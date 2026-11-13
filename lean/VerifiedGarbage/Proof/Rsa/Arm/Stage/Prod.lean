module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Loads
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Views

/-! # The ARMv7 key stages: before `M = d e`

After the loads, the arrays read with `W` words hold `0`, `e`, `d` (`AW1`), and
`e` is the narrow array `2 wE` (`LS.ksE`), from which `RecoverDet.prodW` takes
its rows.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem bytes_lt (m : Mem) (a : Addr) (k : Nat) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a k) < 2 ^ (8 * k) := by
  have := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt m a k)
  rwa [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this

/-- The arrays with `W` words after the loads. -/
def AW1 (P : RP) (σ : State) : Nat → Nat := upd (upd (fun _ => 0) wE P.e) wD (dv P σ)

/-- After the loads: `e` live as the narrow array `2 wE`, and the wide array 14 (`RecoverDet.wZ`) zero. -/
theorem LS.ksE {P : RP} {σ s : State} (h : LS P σ (Aload P σ) s) :
    KS P σ (Aload P σ) [aN, 2 * wE] (AW1 P σ)
      [wZ, wE, wD,
        wM, 14] (fun _ => 0) [] s := by
  have sz := h.bs.pre.sizes
  have kw := sz.kw
  have hn : P.n < 2 ^ (32 * P.w) := by
    have := h.bs.pre.nB ▸ bytes_lt σ.mem (State.addr P.nP) P.K
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have he : P.e < 2 ^ (32 * P.w) := by
    have hb := h.bs.pre.eB ▸ bytes_lt σ.mem (State.addr P.eP) P.el
    have := h.bs.pre.el2
    exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * P.el ≤ 32 * P.w by omega))
  have nw : ∀ j < nArr, Aload P σ j < 2 ^ (32 * P.w) → num s.mem P.B P.w j = Aload P σ j := fun j hj hl => by
    rw [← h.full j hj] at hl ⊢
    exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 hl
  have z : ∀ j < nArr, j ≠ aN → j ≠ 2 * wE →
      j ≠ 2 * wD → num s.mem P.B P.w j = 0 := fun j hj a b c => by
    rw [nw j hj (by simp only [Aload, upd, a, b, c, ↓reduceIte]; exact Nat.two_pow_pos _)]
    simp only [Aload, upd, a, b, c, ↓reduceIte]
  refine ⟨h.bs, h.ws.r8, h.cnt, ?_, ?_, by simp, ?_, ?_, by simp⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact nw _ (by decide) (by simp only [Aload, upd]; simp; exact hn)
    · exact nw _ (by decide) (by simp only [Aload, upd]; simp; exact he)
  · intro j hj
    have zz : ∀ i, i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 29 → num s.mem P.B P.w i = 0 := fun i hi => by
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact z _ (by decide) (by decide) (by decide) (by decide)
    have z28 : num s.mem P.B P.w 28 = 0 := z _ (by decide) (by decide) (by decide) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    all_goals refine (numW_of (h.full _ (by decide)) (zz _ (by decide))).trans ?_
    all_goals simp [Aload, AW1, upd, aN, wE, wD, wZ, wM]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl | rfl | rfl) <;> decide

end VG.Proof.Rsa.Arm.Recover
