import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round

def raw (g : Nat) (a : BitVec 32) : BitVec 32 :=
  (((a + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) + BitVec.ofNat 32 (hbAdd g)) >>> dShift g

theorem raw_toNat {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat < q) :
    (raw g a).toNat = hbF g a.toNat := by
  have hq : q = 8380417 := rfl
  rw [hbF_eq (mem_of_isG hg) ha]
  have hM : hbMul g ≤ 11275 := by rcases hg with rfl | rfl <;> decide
  have hA : hbAdd g ≤ 2 ^ 23 := by rcases hg with rfl | rfl <;> decide
  have hS : dShift g = hbShift g := rfl
  have e1 : ((a + BitVec.ofNat 32 127) >>> 7).toNat = (a.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    congr 1; omega
  have e2 : (((a + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g)).toNat =
      (a.toNat + 127) / 128 * hbMul g := by
    rw [BitVec.toNat_mul, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := hbMul g) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) (hM))
      (by omega))
  have e3 : (((a + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) + BitVec.ofNat 32 (hbAdd g)).toNat =
      (a.toNat + 127) / 128 * hbMul g + hbAdd g := by
    have : (a.toNat + 127) / 128 * hbMul g < 2 ^ 30 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) (hM)) (by omega)
    rw [BitVec.toNat_add, e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := hbAdd g) (by omega)]
    omega
  rw [raw, BitVec.toNat_ushiftRight, e3, Nat.shiftRight_eq_div_pow, hS]


/-- Branchless wrap to zero at the upper decomposition endpoint. -/
def highWord (g : Nat) (a : BitVec 32) : BitVec 32 :=
  let f := raw g a
  f &&& (f - BitVec.ofNat 32 (dMod g)).sshiftRight 31

theorem highWord_toNat {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat < q) :
    (highWord g a).toNat = hbF g a.toNat % hbM g := by
  have hf := raw_toNat hg ha
  have hle := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hm44 : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  have hmod : (BitVec.ofNat 32 (dMod g)).toNat = hbM g := by
    rw [BitVec.toNat_ofNat, dMod_eq hg, Nat.mod_eq_of_lt (by omega)]
  dsimp only [highWord]
  rw [ResidentMask.signMask32]
  by_cases h : hbF g a.toNat < hbM g
  · rw [ite_eq_right (by bv_omega)]
    have hand : raw g a &&& (-1 : BitVec 32) = raw g a := BitVec.and_allOnes
    rw [hand, hf, Nat.mod_eq_of_lt h]
  · rw [ite_eq_left (by bv_omega)]
    have hand : raw g a &&& (0 : BitVec 32) = 0 := BitVec.and_zero
    rw [hand, show hbF g a.toNat = hbM g by omega, Nat.mod_self]
    rfl

/-- Agreement with the original specification on every canonical coefficient. -/
theorem highWord_spec {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat < q) :
    (highWord g a).toNat = (highBits g ⟨a.toNat, ha⟩).toNat := by
  rw [highWord_toNat hg ha, highBits_eq (mem_of_isG hg)]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
