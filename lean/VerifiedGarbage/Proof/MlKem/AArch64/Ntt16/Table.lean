module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM's 16-bit NTT on AArch64: tables of halfwords

A table of halfwords `H`, four to a doubleword (`hw4`): a vector loaded from
it has the halfwords as its lanes (`vhalf_table`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 Impl.MlKem.AArch64.Ntt16

/-- The four halfwords of group `j` of `H`, as a doubleword. -/
def hw4 (H : List Nat) (j : Nat) : BitVec 64 :=
  BitVec.ofNat 16 (H.getD (4 * j + 3) 0) ++ BitVec.ofNat 16 (H.getD (4 * j + 2) 0) ++
    BitVec.ofNat 16 (H.getD (4 * j + 1) 0) ++ BitVec.ofNat 16 (H.getD (4 * j) 0)

/-- A 16-byte load as two doublewords. -/
theorem read16_dw (m : Mem) (a : Addr) :
    m.read a 16 = ofVDwords (m.readW a 64) (m.readW (a + BitVec.ofNat 64 8) 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_read m 16 a i (by omega_using [hi])]
  simp only [ofVDwords, BitVec.getLsbD_append, Mem.readW, BitVec.getLsbD_setWidth]
  by_cases h : i < 64
  · rw [ite_eq_left h, getLsbD_read m 8 a i (by omega_using [h])]; simp [h]
  · rw [ite_eq_right h, getLsbD_read m 8 _ (i - 64) (by omega_using [hi])]
    simp only [show i - 64 < 64 by omega_using [hi], decide_true, Bool.true_and]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 + (i - 64) / 8 = i / 8 by omega_using [h],
      show (i - 64) % 8 = i % 8 by omega_using [h]]

theorem hw4_half (H : List Nat) (j : Nat) {h : Nat} (hh : h < 4) :
    (hw4 H j).extractLsb' (16 * h) 16 = BitVec.ofNat 16 (H.getD (4 * j + h) 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [hw4, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  match h, hh with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_zero]
    all_goals exact congrArg _ (by omega_using [])

/-- Lane `e` of the vector `i` of a table of halfwords. -/
theorem vhalf_table {m : Mem} {p : Addr} {off N : Nat} {H : List Nat}
    (htab : ∀ j < N, m.readW (p + BitVec.ofNat 64 (off + 8 * j)) 64 = hw4 H j) {i : Nat}
    (hi : 2 * i + 1 < N) {e : Nat} (he : e < 8) :
    vhalf (m.read (p + BitVec.ofNat 64 (off + 16 * i)) 16) e = BitVec.ofNat 16 (H.getD (8 * i + e) 0) := by
  rw [read16_dw, BitVec.add_assoc, ← BitVec.ofNat_add,
    show off + 16 * i + 8 = off + 8 * (2 * i + 1) by omega_using [],
    show off + 16 * i = off + 8 * (2 * i) by omega_using [], htab _ (by omega_using [hi]), htab _ hi,
    vhalf_ofVDwords _ _ he]
  by_cases h : e < 4
  · rw [ite_eq_left h, hw4_half _ _ (by omega_using [])]
    exact congrArg (BitVec.ofNat 16) (congrArg (fun k => H.getD k 0) (by omega_using [h]))
  · rw [ite_eq_right h, hw4_half _ _ (by omega_using [])]
    exact congrArg (BitVec.ofNat 16) (congrArg (fun k => H.getD k 0) (by omega_using [he, h]))

end VG.Proof.MlKem.AArch64.Ntt16
