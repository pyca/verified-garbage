module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Byte
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # CBD2 lane arithmetic and widening -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64
open VG.Proof.Rc4.AArch64 (vbyte_map2 vbyte_and)

def broadcast (b : BitVec 8) : BitVec 128 := ofVBytes fun _ => b

def shiftBytes (n : Nat) (x : BitVec 128) : BitVec 128 :=
  VArr.b16.map2 (fun _ _ y => y >>> n) 0 x

def sumBytes (x : BitVec 128) : BitVec 128 :=
  VArr.b16.map2 (fun _ a b => a+b) (x &&& broadcast 0x55) (shiftBytes 1 x &&& broadcast 0x55)

def diffBytes (x : BitVec 128) : BitVec 128 :=
  VArr.b16.map2 (fun _ a b => a-b)
    (VArr.b16.map2 (fun _ a b => a+b) (sumBytes x &&& broadcast 0x33) (broadcast 0x22))
    (shiftBytes 2 (sumBytes x) &&& broadcast 0x33)

theorem byte_differences (x : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (diffBytes x) i = differences (vbyte x i) := by
  simp only [diffBytes, sumBytes, shiftBytes, vbyte_map2 _ _ _ hi, vbyte_and,
    broadcast, vbyte_ofVBytes _ hi, differences, sums]
  rfl

theorem byte_low (x : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (diffBytes x &&& broadcast 15) i = nibble (vbyte x i) false := by
  rw [vbyte_and, byte_differences x hi, broadcast, vbyte_ofVBytes _ hi]
  rfl

theorem byte_high (x : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (shiftBytes 4 (diffBytes x)) i = nibble (vbyte x i) true := by
  rw [shiftBytes, vbyte_map2 _ _ _ hi, byte_differences x hi]
  rfl

theorem half_bytes (x : BitVec 128) (k : Nat) :
    vhalf x k = vbyte x (2*k+1) ++ vbyte x (2*k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vhalf, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and]
  by_cases h : i < 8
  · simp [h, show 8*(2*k)+i = 16*k+i by omega]
  · simp [h, show i-8 < 8 by omega, show 8*(2*k+1)+(i-8) = 16*k+i by omega]

theorem half_zip_zero (x : BitVec 128) {k : Nat} (hk : k < 8) :
    (vhalf (VPermOp.eval .zip1 .b16 x 0) k).toNat = (vbyte x k).toNat ∧
    (vhalf (VPermOp.eval .zip2 .b16 x 0) k).toNat = (vbyte x (8+k)).toNat := by
  rw [half_bytes, half_bytes,
    VG.Proof.Blowfish.AArch64.vbyte_zip1 _ _ (by omega),
    VG.Proof.Blowfish.AArch64.vbyte_zip1 _ _ (by omega),
    VG.Proof.Blowfish.AArch64.vbyte_zip2 _ _ (by omega),
    VG.Proof.Blowfish.AArch64.vbyte_zip2 _ _ (by omega)]
  simp only [show (2*k+1)%2 = 1 by omega, show (2*k)%2 = 0 by omega,
    show (2*k+1)/2 = k by omega, show (2*k)/2 = k by omega,
    ite_true, show ¬ (1 = 0) by decide, ite_false]
  constructor <;> rw [BitVec.toNat_append] <;> simp [vbyte]

/-- Interleaving the low and high nibbles preserves their coefficient order. -/
theorem byte_zip_nibbles (x : BitVec 128) {k : Nat} (hk : k < 16) :
    vbyte (VPermOp.eval .zip1 .b16 (diffBytes x &&& broadcast 15)
      (shiftBytes 4 (diffBytes x))) k = nibble (vbyte x (k/2)) (k%2 != 0) ∧
    vbyte (VPermOp.eval .zip2 .b16 (diffBytes x &&& broadcast 15)
      (shiftBytes 4 (diffBytes x))) k = nibble (vbyte x (8+k/2)) (k%2 != 0) := by
  rw [VG.Proof.Blowfish.AArch64.vbyte_zip1 _ _ hk,
    VG.Proof.Blowfish.AArch64.vbyte_zip2 _ _ hk]
  by_cases h : k%2 = 0
  · simp only [h, ite_true, bne_self_eq_false]
    exact ⟨byte_low x (by omega), byte_low x (by omega)⟩
  · simp only [h, ite_false, show (k%2 != 0) = true from bne_iff_ne.mpr h]
    exact ⟨byte_high x (by omega), byte_high x (by omega)⟩

/-- Two zero interleaves widen each byte into a word without changing it. -/
theorem word_widen (x : BitVec 128) {k : Nat} (hk : k < 4) :
    (vword (VPermOp.eval .zip1 .h8 (VPermOp.eval .zip1 .b16 x 0) 0) k).toNat =
      (vbyte x k).toNat ∧
    (vword (VPermOp.eval .zip2 .h8 (VPermOp.eval .zip1 .b16 x 0) 0) k).toNat =
      (vbyte x (4+k)).toNat ∧
    (vword (VPermOp.eval .zip1 .h8 (VPermOp.eval .zip2 .b16 x 0) 0) k).toNat =
      (vbyte x (8+k)).toNat ∧
    (vword (VPermOp.eval .zip2 .h8 (VPermOp.eval .zip2 .b16 x 0) 0) k).toNat =
      (vbyte x (12+k)).toNat := by
  have z : ∀ e < 8, vhalf 0 e = 0 := by intro e _; simp [vhalf]
  obtain ⟨h1,h2⟩ := VG.Proof.MlKem.AArch64.Ntt16.vword_zip_zero
    (x := VPermOp.eval .zip1 .b16 x 0) z hk
  obtain ⟨h3,h4⟩ := VG.Proof.MlKem.AArch64.Ntt16.vword_zip_zero
    (x := VPermOp.eval .zip2 .b16 x 0) z hk
  rw [h1,h2,h3,h4, (half_zip_zero x (by omega : k < 8)).1,
    (half_zip_zero x (by omega : 4+k < 8)).1,
    (half_zip_zero x (by omega : k < 8)).2,
    (half_zip_zero x (by omega : 4+k < 8)).2]
  simp only [show 8+(4+k) = 12+k by omega, and_self]

end VG.Proof.MlKem.AArch64.Cbd16
