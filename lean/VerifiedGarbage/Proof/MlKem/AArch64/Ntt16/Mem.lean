module
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.Mem
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM's 16-bit NTT on AArch64: polynomials in halfwords

Eight coefficients of a polynomial (`u32`s) narrowed into the halfwords of a
vector (`uzp1`, `rep_load`), a vector of halfwords widened back into four
coefficients (`zip1`, `zip2` with zero, `vword_zip_zero`), and a vector read
back where it was stored (`read_write16`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem

theorem read_write16 (m : Mem) (a : Addr) (x : BitVec 128) : (m.write a 16 x).read a 16 = x := by
  refine Mem.read_eq_of_bytes fun i hi => ?_
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega), hi, ite_true]

/-- A word as its two halfwords. -/
theorem vword_halves (x : BitVec 128) (k : Nat) : vword x k = vhalf x (2 * k + 1) ++ vhalf x (2 * k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 16
  · rw [ite_eq_left h, ← vword_lo, BitVec.getLsbD_extractLsb']; simp [h]
  · rw [ite_eq_right h, ← vword_hi, BitVec.getLsbD_extractLsb']
    simp only [show i - 16 < 16 by omega, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

/-- The low halfword of a coefficient less than `2¹⁵`, as a signed number. -/
theorem toInt_lo {w : BitVec 32} (hw : w.toNat < 32768) : (w.extractLsb' 0 16).toInt = w.toNat := by
  have : (w.extractLsb' 0 16).toNat = w.toNat := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toInt_eq_toNat_of_lt (by omega), this]

/-- Eight coefficients from `j`, narrowed to halfwords. -/
theorem rep_load {m : Mem} {p : Addr} {P : Poly} (h : PolyIs m p P) {j : Nat} (hj : j + 8 ≤ 256) :
    Rep (VPermOp.eval .uzp1 .h8 (m.read (coeffAddr p j) 16) (m.read (coeffAddr p (j + 4)) 16))
      (fun e => P[j + e]!) 3329 := fun e he => by
  have l0 := lanes_load h (j := j) (by omega)
  have l1 := lanes_load h (j := j + 4) (by omega)
  rw [vhalf_perm_h8 _ _ _ he]
  have key : ∀ (x : BitVec 128) (k : Nat), k < 4 → (vword x k).toNat = (P[j + e]!).val →
      LRep (vhalf x (2 * k)) (P[j + e]!) 3329 := fun x k _ hx => by
    have hv := val_lt (P[j + e]!)
    rw [LRep, ← vword_lo, toInt_lo (by omega), hx]
    exact ⟨by omega, by omega, by simp⟩
  by_cases c : e < 4
  · rw [ite_eq_left c]; exact key _ e c (l0 e c)
  · rw [ite_eq_right c, show 2 * e - 8 = 2 * (e - 4) by omega]
    have := l1 (e - 4) (by omega)
    simp only [show j + 4 + (e - 4) = j + e by omega] at this
    exact key _ (e - 4) (by omega) this

/-- `zip1` or `zip2` of `x` with zero: words `k` (or `4 + k`) of `x`'s halfwords, zero-extended. -/
theorem vword_zip_zero {x z : BitVec 128} (hz : ∀ e < 8, vhalf z e = 0) {k : Nat} (hk : k < 4) :
    (vword (VPermOp.eval .zip1 .h8 x z) k).toNat = (vhalf x k).toNat ∧
    (vword (VPermOp.eval .zip2 .h8 x z) k).toNat = (vhalf x (4 + k)).toNat := by
  rw [vword_halves, vword_halves, vhalf_perm_h8 _ _ _ (by omega), vhalf_perm_h8 _ _ _ (by omega),
    vhalf_perm_h8 _ _ _ (by omega), vhalf_perm_h8 _ _ _ (by omega)]
  simp only [show (2 * k + 1) % 2 = 1 by omega, show (2 * k) % 2 = 0 by omega, ite_true,
    show ¬ (1 = 0) by decide, ite_false, show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega,
    hz k (by omega), hz (4 + k) (by omega)]
  constructor <;> rw [BitVec.toNat_append] <;> simp

end VG.Proof.MlKem.AArch64.Ntt16
