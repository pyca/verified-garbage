module

import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.NttLayer

/-!
# ML-KEM on AArch64: the lanes of the inverse NTT, reduced

A lane of the 16-bit inverse NTT reduced to less than `q` in absolute value
represents the same coefficient (`n1W_rep`), and made nonnegative is its
value (`normL_val`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (LRep gs_lane mm_ok ofNat_zeta zeta_lt nonneg_lane)

/-! ## The coefficients represent `NTT⁻¹`'s -/

/-- A lane reduced to less than `q` in absolute value. -/
theorem n1W_rep {a : BitVec 16} {X : Zq} {B : Nat} (h : LRep a X B) (hB : B ≤ 32768) : LRep (n1W a) X 3329 := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok a (z := 1) (by omega_arith) (by decide)
  have e1 : n1W a = a - T * BitVec.ofNat 16 3329 := by
    unfold n1W qdW
    rw [show (BitVec.ofNat 16 10) = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw 1) from rfl, hT]
    rfl
  rw [show a * BitVec.ofNat 16 1 = a from BitVec.mul_one _] at b1 b2 b3
  rw [e1]
  refine ⟨b1, b2, ?_⟩
  omega_arith

/-- `a`, less than `q` in absolute value, made nonnegative, is its value. -/
theorem normL_val {x : BitVec 16} {X : Zq} (h : LRep x X 3329) : (normL x).toNat = X.val := by
  obtain ⟨b1, b2, b3⟩ := h
  have hn := nonneg_lane b1 b2
  unfold normL
  rw [show BitVec.ofNat 16 qN = BitVec.ofNat 16 3329 from rfl]
  have hX : X.val < 3329 := X.isLt
  have hv : (x + (x.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt = (X.val : Int) := by
    rw [hn]
    split <;> omega_arith
  generalize x + (x.sshiftRight 15 &&& BitVec.ofNat 16 3329) = y at hv ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hv
  split at hv <;> omega_arith

end VG.Proof.MlKem.AArch64.NttR
