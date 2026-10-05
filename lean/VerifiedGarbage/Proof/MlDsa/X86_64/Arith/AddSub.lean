import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Common
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VArith`. -/
section

/-!
# ML-DSA on x86-64: arithmetic modulo `q` in doublewords

What `vmont`, `vcadd` and `vcsub` (`Impl/MlDsa/X86_64/Arith/Vec.lean`) compute
in each doubleword:

* `montV d z zo`, the register `vmont` leaves: each doubleword is `mont` of
  the product of those of `d` and `z` (`dword_montV`), if the even
  doublewords of `zo` are the odd ones of `z` and each product is less than
  `q · 2³²` (each quadword product `P` becomes `P + m · q`, which is
  `mont P · 2³²`: `redc_toNat`);
* `caddL`, `csubL`: a doubleword plus `q` if it is negative, and less `q`
  first, which `condSub` describes (`csubL_toNat`, `subD_toNat`,
  `addD_toNat`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

/-! ## Quadwords -/

theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem qword_app1 (a b : BitVec 64) : qword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem dword_lo (x : BitVec 128) (i : Nat) : dword x (2 * i) = (qword x i).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 0 + j < 64 by omega)]
  exact congrArg _ (by omega)

theorem dword_hi (x : BitVec 128) (i : Nat) : dword x (2 * i + 1) = (qword x i).extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 32 + j < 64 by omega)]
  exact congrArg _ (by omega)

/-- The low doubleword of a quadword, zero-extended. -/
def lo32 (x : BitVec 64) : BitVec 64 := (x.extractLsb' 0 32).setWidth 64

theorem lo32_toNat (x : BitVec 64) : (VG.Proof.MlDsa.X86_64.Arith.lo32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [VG.Proof.MlDsa.X86_64.Arith.lo32, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem qword_paddq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .paddq x y) i = qword x i + qword y i := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [XBinOp.eval, VG.Proof.MlDsa.X86_64.Arith.qword_app0]
  · simp only [XBinOp.eval, VG.Proof.MlDsa.X86_64.Arith.qword_app1]

theorem qword_pmuludq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pmuludq x y) i = VG.Proof.MlDsa.X86_64.Arith.lo32 (qword x i) * VG.Proof.MlDsa.X86_64.Arith.lo32 (qword y i) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [XBinOp.eval, VG.Proof.MlDsa.X86_64.Arith.qword_app0, VG.Proof.MlDsa.X86_64.Arith.lo32, ← VG.Proof.MlDsa.X86_64.Arith.dword_lo]
  · simp only [XBinOp.eval, VG.Proof.MlDsa.X86_64.Arith.qword_app1, VG.Proof.MlDsa.X86_64.Arith.lo32, ← VG.Proof.MlDsa.X86_64.Arith.dword_lo]

theorem qword_psrlq32 (x : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq x 32) i = qword x i >>> 32 := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [XShiftOp.eval, show ¬ 63 < (32 : BitVec 8).toNat by decide, ite_false, VG.Proof.MlDsa.X86_64.Arith.qword_app0]; rfl
  · simp only [XShiftOp.eval, show ¬ 63 < (32 : BitVec 8).toNat by decide, ite_false, VG.Proof.MlDsa.X86_64.Arith.qword_app1]; rfl

theorem toNat_lo32_mul (x y : BitVec 64) : (VG.Proof.MlDsa.X86_64.Arith.lo32 x * VG.Proof.MlDsa.X86_64.Arith.lo32 y).toNat = x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) := by
  rw [BitVec.toNat_mul, VG.Proof.MlDsa.X86_64.Arith.lo32_toNat, VG.Proof.MlDsa.X86_64.Arith.lo32_toNat]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by decide)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h1 h2) (by decide))

/-! ## Montgomery reduction of a quadword -/

/-- `q` in each doubleword. -/
def qV : BitVec 128 := 0x007FE001007FE001007FE001007FE001#128

/-- `-q⁻¹ mod 2³²` in each doubleword. -/
def qinvV : BitVec 128 := 0xFC7FDFFFFC7FDFFFFC7FDFFFFC7FDFFF#128

theorem lo32_qword_qV {i : Nat} (hi : i < 2) : (VG.Proof.MlDsa.X86_64.Arith.lo32 (qword VG.Proof.MlDsa.X86_64.Arith.qV i)).toNat = q := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

theorem lo32_qword_qinvV {i : Nat} (hi : i < 2) : (VG.Proof.MlDsa.X86_64.Arith.lo32 (qword VG.Proof.MlDsa.X86_64.Arith.qinvV i)).toNat = montQInv := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

/-- `vredc` on a quadword `x`: `x + m · q`. -/
def redc (x qi qq : BitVec 64) : BitVec 64 := x + VG.Proof.MlDsa.X86_64.Arith.lo32 (VG.Proof.MlDsa.X86_64.Arith.lo32 x * VG.Proof.MlDsa.X86_64.Arith.lo32 qi) * VG.Proof.MlDsa.X86_64.Arith.lo32 qq

theorem redc_toNat {x qi qq : BitVec 64} (hqi : (VG.Proof.MlDsa.X86_64.Arith.lo32 qi).toNat = montQInv) (hqq : (VG.Proof.MlDsa.X86_64.Arith.lo32 qq).toNat = q)
    (hx : x.toNat < q * 2 ^ 32) : (VG.Proof.MlDsa.X86_64.Arith.redc x qi qq).toNat = mont x.toNat * 2 ^ 32 := by
  have hm : (VG.Proof.MlDsa.X86_64.Arith.lo32 (VG.Proof.MlDsa.X86_64.Arith.lo32 x * VG.Proof.MlDsa.X86_64.Arith.lo32 qi)).toNat = montM x.toNat := by
    rw [VG.Proof.MlDsa.X86_64.Arith.lo32_toNat, BitVec.toNat_mul, VG.Proof.MlDsa.X86_64.Arith.lo32_toNat, hqi, montM, Nat.mod_mod_of_dvd _ (by decide)]
  have hmq : (VG.Proof.MlDsa.X86_64.Arith.lo32 (VG.Proof.MlDsa.X86_64.Arith.lo32 x * VG.Proof.MlDsa.X86_64.Arith.lo32 qi) * VG.Proof.MlDsa.X86_64.Arith.lo32 qq).toNat = montM x.toNat * q := by
    rw [BitVec.toNat_mul, hm, hqq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (montM_lt _) (by decide))
      (by decide))
  rw [VG.Proof.MlDsa.X86_64.Arith.redc, BitVec.toNat_add, hmq, ← mont_mul]
  have := mont_lt hx
  rw [q_eq] at this
  exact Nat.mod_eq_of_lt (by omega)

theorem redc_hi {x qi qq : BitVec 64} (hqi : (VG.Proof.MlDsa.X86_64.Arith.lo32 qi).toNat = montQInv) (hqq : (VG.Proof.MlDsa.X86_64.Arith.lo32 qq).toNat = q)
    (hx : x.toNat < q * 2 ^ 32) : ((VG.Proof.MlDsa.X86_64.Arith.redc x qi qq).extractLsb' 32 32).toNat = mont x.toNat := by
  rw [BitVec.extractLsb'_toNat, VG.Proof.MlDsa.X86_64.Arith.redc_toNat hqi hqq hx, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (by decide)]
  have := mont_lt hx
  rw [q_eq] at this
  exact Nat.mod_eq_of_lt (by omega)

theorem redc_lo {x qi qq : BitVec 64} (hqi : (VG.Proof.MlDsa.X86_64.Arith.lo32 qi).toNat = montQInv) (hqq : (VG.Proof.MlDsa.X86_64.Arith.lo32 qq).toNat = q)
    (hx : x.toNat < q * 2 ^ 32) : (VG.Proof.MlDsa.X86_64.Arith.redc x qi qq).extractLsb' 0 32 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, VG.Proof.MlDsa.X86_64.Arith.redc_toNat hqi hqq hx, Nat.shiftRight_zero, Nat.mul_mod_left]
  rfl

theorem or_zero_toNat (x : BitVec 32) : (x ||| 0).toNat = x.toNat := by
  simp

theorem zero_or_toNat (x : BitVec 32) : ((0 : BitVec 32) ||| x).toNat = x.toNat := by
  simp

theorem lo_shr32 (x : BitVec 64) : ((x >>> 32).extractLsb' 0 32).toNat = (x.extractLsb' 32 32).toNat := by
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero]

theorem hi_shr32 (x : BitVec 64) : (x >>> 32).extractLsb' 32 32 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  have := x.isLt
  rw [Nat.div_eq_of_lt (by omega)]; rfl

/-! ## `vmont` -/

/-- The register `vmont d z zo` leaves in `d`. -/
def montV (d z zo : BitVec 128) : BitVec 128 :=
  let u := shufDwords d 0xF5
  let a := XBinOp.eval .pmuludq d z
  let b := XBinOp.eval .pmuludq u zo
  XBinOp.eval .por
    (XShiftOp.eval .psrlq (XBinOp.eval .paddq a (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq a VG.Proof.MlDsa.X86_64.Arith.qinvV) VG.Proof.MlDsa.X86_64.Arith.qV)) 32)
    (XBinOp.eval .paddq b (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq b VG.Proof.MlDsa.X86_64.Arith.qinvV) VG.Proof.MlDsa.X86_64.Arith.qV))

theorem qword_vredc (a : BitVec 128) {j : Nat} (hj : j < 2) :
    qword (XBinOp.eval .paddq a (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq a VG.Proof.MlDsa.X86_64.Arith.qinvV) VG.Proof.MlDsa.X86_64.Arith.qV)) j =
      VG.Proof.MlDsa.X86_64.Arith.redc (qword a j) (qword VG.Proof.MlDsa.X86_64.Arith.qinvV j) (qword VG.Proof.MlDsa.X86_64.Arith.qV j) := by
  rw [VG.Proof.MlDsa.X86_64.Arith.qword_paddq _ _ hj, VG.Proof.MlDsa.X86_64.Arith.qword_pmuludq _ _ hj, VG.Proof.MlDsa.X86_64.Arith.qword_pmuludq _ _ hj]; rfl

theorem toNat_qword_pmuludq (x y : BitVec 128) {j : Nat} (hj : j < 2) :
    (qword (XBinOp.eval .pmuludq x y) j).toNat = (dword x (2 * j)).toNat * (dword y (2 * j)).toNat := by
  rw [VG.Proof.MlDsa.X86_64.Arith.qword_pmuludq _ _ hj, VG.Proof.MlDsa.X86_64.Arith.toNat_lo32_mul, VG.Proof.MlDsa.X86_64.Arith.dword_lo, VG.Proof.MlDsa.X86_64.Arith.dword_lo, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero]

/-- Each doubleword of `montV d z zo` is `mont` of the product of those of
`d` and `z`. -/
theorem dword_montV {d z zo : BitVec 128} (hzo : ∀ j < 2, dword zo (2 * j) = dword z (2 * j + 1))
    (hb : ∀ i < 4, (dword d i).toNat * (dword z i).toNat < q * 2 ^ 32) {i : Nat} (hi : i < 4) :
    (dword (VG.Proof.MlDsa.X86_64.Arith.montV d z zo) i).toNat = mont ((dword d i).toNat * (dword z i).toNat) := by
  have hqi : ∀ j < 2, (VG.Proof.MlDsa.X86_64.Arith.lo32 (qword VG.Proof.MlDsa.X86_64.Arith.qinvV j)).toNat = montQInv := fun j hj => VG.Proof.MlDsa.X86_64.Arith.lo32_qword_qinvV hj
  have hqq : ∀ j < 2, (VG.Proof.MlDsa.X86_64.Arith.lo32 (qword VG.Proof.MlDsa.X86_64.Arith.qV j)).toNat = q := fun j hj => VG.Proof.MlDsa.X86_64.Arith.lo32_qword_qV hj
  rw [VG.Proof.MlDsa.X86_64.Arith.montV, dword_por]
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j < 2, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega, by omega⟩
  all_goals
    have hx : (qword (XBinOp.eval .pmuludq d z) j).toNat = (dword d (2 * j)).toNat * (dword z (2 * j)).toNat :=
      VG.Proof.MlDsa.X86_64.Arith.toNat_qword_pmuludq d z hj
    have hy : (qword (XBinOp.eval .pmuludq (shufDwords d 0xF5) zo) j).toNat =
        (dword d (2 * j + 1)).toNat * (dword z (2 * j + 1)).toNat := by
      rw [VG.Proof.MlDsa.X86_64.Arith.toNat_qword_pmuludq _ _ hj, hzo j hj, dword_shufDwords _ _ (by omega)]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  · -- an even doubleword: the quotient of the even product, moved down
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_lo, VG.Proof.MlDsa.X86_64.Arith.dword_lo, VG.Proof.MlDsa.X86_64.Arith.qword_psrlq32 _ hj, VG.Proof.MlDsa.X86_64.Arith.qword_vredc _ hj, VG.Proof.MlDsa.X86_64.Arith.qword_vredc _ hj,
      VG.Proof.MlDsa.X86_64.Arith.redc_lo (hqi j hj) (hqq j hj) (by rw [hy]; exact hb _ (by omega)), VG.Proof.MlDsa.X86_64.Arith.or_zero_toNat, VG.Proof.MlDsa.X86_64.Arith.lo_shr32,
      VG.Proof.MlDsa.X86_64.Arith.redc_hi (hqi j hj) (hqq j hj) (by rw [hx]; exact hb _ (by omega)), hx]
  · -- an odd doubleword: the quotient of the odd product, in place
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_hi, VG.Proof.MlDsa.X86_64.Arith.dword_hi, VG.Proof.MlDsa.X86_64.Arith.qword_psrlq32 _ hj, VG.Proof.MlDsa.X86_64.Arith.hi_shr32, VG.Proof.MlDsa.X86_64.Arith.zero_or_toNat, VG.Proof.MlDsa.X86_64.Arith.qword_vredc _ hj,
      VG.Proof.MlDsa.X86_64.Arith.redc_hi (hqi j hj) (hqq j hj) (by rw [hy]; exact hb _ (by omega)), hy]

/-! ## Conditional additions and subtractions of `q` -/

/-- `q` as a doubleword. -/
def qB : BitVec 32 := 8380417#32

theorem dword_qV {i : Nat} (hi : i < 4) : dword VG.Proof.MlDsa.X86_64.Arith.qV i = VG.Proof.MlDsa.X86_64.Arith.qB := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

/-- `vcadd` on a doubleword: `d + q` if `d` is negative (as a signed doubleword). -/
def caddL (d : BitVec 32) : BitVec 32 := d + (d.sshiftRight (min (31 : BitVec 8).toNat 32) &&& VG.Proof.MlDsa.X86_64.Arith.qB)

/-- `vcsub` on a doubleword. -/
def csubL (d : BitVec 32) : BitVec 32 := VG.Proof.MlDsa.X86_64.Arith.caddL (d - VG.Proof.MlDsa.X86_64.Arith.qB)

theorem sshiftRight31 (d : BitVec 32) :
    d.sshiftRight (min (31 : BitVec 8).toNat 32) = if d.toNat < 2 ^ 31 then 0 else -1 := by
  rw [show min (31 : BitVec 8).toNat 32 = 31 from rfl]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, MlKem.X86_64.W.toInt32]
  have := d.isLt
  split
  · rw [show (0 : BitVec 32).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega
  · rw [show (-1 : BitVec 32).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega

theorem caddL_toNat (d : BitVec 32) :
    (VG.Proof.MlDsa.X86_64.Arith.caddL d).toNat = if d.toNat < 2 ^ 31 then d.toNat else (d.toNat + q) % 2 ^ 32 := by
  rw [VG.Proof.MlDsa.X86_64.Arith.caddL, VG.Proof.MlDsa.X86_64.Arith.sshiftRight31]
  split
  · rw [show (0 : BitVec 32) &&& VG.Proof.MlDsa.X86_64.Arith.qB = 0 by decide]; exact congrArg BitVec.toNat (BitVec.add_zero d)
  · rw [show (-1 : BitVec 32) &&& VG.Proof.MlDsa.X86_64.Arith.qB = VG.Proof.MlDsa.X86_64.Arith.qB by decide, BitVec.toNat_add]; rfl

/-- `vcsub` reduces a doubleword less than `2q`. -/
theorem csubL_toNat {d : BitVec 32} (h : d.toNat < 2 * q) : (VG.Proof.MlDsa.X86_64.Arith.csubL d).toNat = condSub d.toNat := by
  have e : (d - VG.Proof.MlDsa.X86_64.Arith.qB).toNat = (d.toNat + 2 ^ 32 - q) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]; rw [q_eq] at *; simp only [VG.Proof.MlDsa.X86_64.Arith.qB, BitVec.toNat_ofNat]; omega
  rw [VG.Proof.MlDsa.X86_64.Arith.csubL, VG.Proof.MlDsa.X86_64.Arith.caddL_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega

/-- The sum of two reduced doublewords, reduced by `vcsub`. -/
theorem addD_toNat {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Arith.csubL (a + b)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add]; rw [q_eq] at *; omega
  rw [VG.Proof.MlDsa.X86_64.Arith.csubL_toNat (by rw [e]; omega), e]

/-- The difference of two reduced doublewords, reduced by `vcadd`. -/
theorem subD_toNat {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Arith.caddL (a - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a - b).toNat = (a.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega
  rw [VG.Proof.MlDsa.X86_64.Arith.caddL_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega

/-- `b - a + q` of two reduced doublewords, which `vibfly` multiplies by the zeta. -/
theorem subq_toNat {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (b - a + VG.Proof.MlDsa.X86_64.Arith.qB).toNat = b.toNat + q - a.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_sub]; rw [q_eq] at *; simp only [VG.Proof.MlDsa.X86_64.Arith.qB, BitVec.toNat_ofNat]; omega

/-! ## Butterflies, lane by lane -/

/-- A product by a zeta in Montgomery form, reduced: `ζ · y`. -/
theorem mulZ {b z m : BitVec 32} {y ζ : Spec.MlDsa.Zq} (hb : b.toNat = y.val) (hz : z.toNat = ζ.val * 2 ^ 32 % q)
    (hm : m.toNat = mont (b.toNat * z.toNat)) : (VG.Proof.MlDsa.X86_64.Arith.csubL m).toNat = (ζ * y).val := by
  have hx : b.toNat * z.toNat < q * 2 ^ 32 := by
    rw [hb, hz]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt y) (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
      (by decide)) (by decide)
  rw [VG.Proof.MlDsa.X86_64.Arith.csubL_toNat (by rw [hm]; exact mont_lt hx), hm, condSub_mont hx, hb, hz, mont_mulR, val_mul,
    Nat.mul_comm]

/-- The lanes of `vbfly`: `x + ζ · y` and `x - ζ · y`, from `t = ζ · y`. -/
theorem bflyD {a t : BitVec 32} {x y ζ : Spec.MlDsa.Zq} (ha : a.toNat = x.val) (ht : t.toNat = (ζ * y).val) :
    (VG.Proof.MlDsa.X86_64.Arith.csubL (a + t)).toNat = (x + ζ * y).val ∧ (VG.Proof.MlDsa.X86_64.Arith.caddL (a - t)).toNat = (x - ζ * y).val := by
  have hx := val_lt x
  have hzy := val_lt (ζ * y)
  rw [VG.Proof.MlDsa.X86_64.Arith.addD_toNat (by rw [ha]; exact hx) (by rw [ht]; exact hzy),
    VG.Proof.MlDsa.X86_64.Arith.subD_toNat (by rw [ha]; exact hx) (by rw [ht]; exact hzy), ha, ht, val_add, val_sub]
  exact ⟨rfl, rfl⟩

/-- The lanes of `vibfly`: `x + y` and `ζ · (y - x)`. -/
theorem ibflyD {a b z m : BitVec 32} {x y ζ : Spec.MlDsa.Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 2 ^ 32 % q) (hm : m.toNat = mont ((b - a + VG.Proof.MlDsa.X86_64.Arith.qB).toNat * z.toNat)) :
    (VG.Proof.MlDsa.X86_64.Arith.csubL (a + b)).toNat = (x + y).val ∧ (VG.Proof.MlDsa.X86_64.Arith.csubL m).toNat = (ζ * (y - x)).val := by
  have hx := val_lt x
  have hy := val_lt y
  have e := VG.Proof.MlDsa.X86_64.Arith.subq_toNat (a := a) (b := b) (by rw [ha]; exact hx) (by rw [hb]; exact hy)
  refine ⟨by rw [VG.Proof.MlDsa.X86_64.Arith.addD_toNat (by rw [ha]; exact hx) (by rw [hb]; exact hy), ha, hb, val_add], ?_⟩
  have hb' : (b - a + VG.Proof.MlDsa.X86_64.Arith.qB).toNat < q * 2 ^ 32 := by rw [e, ha, hb]; rw [q_eq] at *; omega
  have hx' : (b - a + VG.Proof.MlDsa.X86_64.Arith.qB).toNat * z.toNat < q * 2 ^ 32 := by
    rw [hz]; rw [e, ha, hb] at hb' ⊢
    have := Nat.mod_lt (ζ.val * 2 ^ 32) (show 0 < q by decide)
    rw [q_eq] at *
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (show y.val + 8380417 - x.val < 2 * 8380417 by omega)
      (Nat.le_of_lt this) (by decide)) (by decide)
  rw [VG.Proof.MlDsa.X86_64.Arith.csubL_toNat (by rw [hm]; exact mont_lt hx'), hm, condSub_mont hx', hz, mont_mulR, e, ha, hb,
    val_mul, val_sub', Nat.mul_mod_mod, Nat.mul_comm ζ.val,
    Nat.add_sub_assoc (Nat.le_of_lt x.isLt) y.val]

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes`. -/
section

/-!
# ML-DSA on x86-64: coefficients in the doublewords of SSE registers

A register holds four coefficients (`DLanes`), and the butterflies `vbfly` and
`vibfly` compute four butterflies of the specification at once (`vbfly_ok`,
`vibfly_ok`), from `q` and `-q⁻¹` in `xmm15` and `xmm14` (`VConsts`), with the
zetas in Montgomery form in `xmm13` (`ZLanes`) and its odd doublewords in the
even ones of `xmm12` (`ZOdd`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly XKeep xmm_setXmm mxcsr_setXmm ifp ifn)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q Zq)

/-- The doublewords of `x` are the values of the coefficients `f 0, …, f 3`. -/
def DLanes (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ i < 4, (dword x i).toNat = (f i).val

/-- The doublewords of `x` are the zetas `ζ i · 2³² mod q` (Montgomery form). -/
def ZLanes (x : BitVec 128) (ζ : Nat → Zq) : Prop := ∀ i < 4, (dword x i).toNat = (ζ i).val * 2 ^ 32 % q

/-- The even doublewords of `zo` are the odd ones of `z`. -/
def ZOdd (z zo : BitVec 128) : Prop := ∀ j < 2, dword zo (2 * j) = dword z (2 * j + 1)

/-- The constants of the vector code are in place. -/
structure VConsts (s : State) : Prop where
  q : s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV
  qinv : s.xmm .xmm14 = VG.Proof.MlDsa.X86_64.Arith.qinvV

theorem VConsts.setXmm {s : State} (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s) {d : XReg} (h14 : XReg.xmm14 ≠ d)
    (h15 : XReg.xmm15 ≠ d) (v : BitVec 128) : VG.Proof.MlDsa.X86_64.Arith.VConsts (s.setXmm d v) :=
  ⟨by rw [xmm_setXmm, ifn h15]; exact hc.q, by rw [xmm_setXmm, ifn h14]; exact hc.qinv⟩

theorem xonly_vconsts {rs : List XReg} {s s' : State} (h : XOnly rs s s') (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : VG.Proof.MlDsa.X86_64.Arith.VConsts s' :=
  ⟨by rw [h.xmm _ h15, hc.q], by rw [h.xmm _ h14, hc.qinv]⟩

/-! ## Registers -/

/-- `vcadd` on a register. -/
def caddV (d : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd d (XBinOp.eval .pand (XShiftOp.eval .psrad d 31) VG.Proof.MlDsa.X86_64.Arith.qV)

/-- `vcsub` on a register. -/
def csubV (d : BitVec 128) : BitVec 128 := VG.Proof.MlDsa.X86_64.Arith.caddV (XBinOp.eval .psubd d VG.Proof.MlDsa.X86_64.Arith.qV)

theorem dword_psubd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .psubd a b) i = dword a i - dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_pand (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .pand a b) i = dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_psrad (a : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrad a n) i = (dword a i).sshiftRight (min n.toNat 32) := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval]

theorem dword_caddV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (VG.Proof.MlDsa.X86_64.Arith.caddV d) i = VG.Proof.MlDsa.X86_64.Arith.caddL (dword d i) := by
  rw [VG.Proof.MlDsa.X86_64.Arith.caddV, dword_paddd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_pand, VG.Proof.MlDsa.X86_64.Arith.dword_psrad _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_qV hi]; rfl

theorem dword_csubV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (VG.Proof.MlDsa.X86_64.Arith.csubV d) i = VG.Proof.MlDsa.X86_64.Arith.csubL (dword d i) := by
  rw [VG.Proof.MlDsa.X86_64.Arith.csubV, VG.Proof.MlDsa.X86_64.Arith.dword_caddV _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_psubd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_qV hi]; rfl

/-- A reduced coefficient times a zeta in Montgomery form is less than `q · 2³²`. -/
theorem prod_lt {y z : BitVec 128} {f ζ : Nat → Zq} (hy : VG.Proof.MlDsa.X86_64.Arith.DLanes y f) (hz : VG.Proof.MlDsa.X86_64.Arith.ZLanes z ζ) :
    ∀ i < 4, (dword y i).toNat * (dword z i).toNat < q * 2 ^ 32 := fun i hi => by
  rw [hy i hi, hz i hi]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt (f i)) (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
    (by decide)) (by decide)

theorem subq_mul_lt {a b c : Nat} (ha : a < 8380417) (hb : b < 8380417) (hc : c < q) :
    (b + q - a) * c < q * 2 ^ 32 := by
  rw [q_eq] at *
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (show b + 8380417 - a < 2 * 8380417 by omega)
    (Nat.le_of_lt hc) (by decide)) (by decide)

theorem eval_movdqa (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

/-! ## Butterflies -/

theorem vbfly_ok {s : State} (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s) {x y ζ : Nat → Zq} (hx : VG.Proof.MlDsa.X86_64.Arith.DLanes (s.xmm .xmm0) x)
    (hy : VG.Proof.MlDsa.X86_64.Arith.DLanes (s.xmm .xmm1) y) (hz : VG.Proof.MlDsa.X86_64.Arith.ZLanes (s.xmm .xmm13) ζ) (ho : VG.Proof.MlDsa.X86_64.Arith.ZOdd (s.xmm .xmm13) (s.xmm .xmm12)) :
    WP isa (.block vbfly) s fun s' => VG.Proof.MlDsa.X86_64.Arith.DLanes (s'.xmm .xmm0) (fun i => x i + ζ i * y i) ∧
      VG.Proof.MlDsa.X86_64.Arith.DLanes (s'.xmm .xmm3) (fun i => x i - ζ i * y i) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' := by
  simp only [vbfly, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [VG.Proof.MlDsa.X86_64.Arith.eval_movdqa]
  rw [hc.q, hc.qinv]
  refine ⟨?_, ?_, by xonly⟩
  · change VG.Proof.MlDsa.X86_64.Arith.DLanes (VG.Proof.MlDsa.X86_64.Arith.csubV (XBinOp.eval .paddd (s.xmm .xmm0)
      (VG.Proof.MlDsa.X86_64.Arith.csubV (VG.Proof.MlDsa.X86_64.Arith.montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))))) _
    intro i hi
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_csubV _ hi, dword_paddd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_csubV _ hi]
    exact (VG.Proof.MlDsa.X86_64.Arith.bflyD (hx i hi) (VG.Proof.MlDsa.X86_64.Arith.mulZ (hy i hi) (hz i hi) (VG.Proof.MlDsa.X86_64.Arith.dword_montV ho (VG.Proof.MlDsa.X86_64.Arith.prod_lt hy hz) hi))).1
  · change VG.Proof.MlDsa.X86_64.Arith.DLanes (VG.Proof.MlDsa.X86_64.Arith.caddV (XBinOp.eval .psubd (s.xmm .xmm0)
      (VG.Proof.MlDsa.X86_64.Arith.csubV (VG.Proof.MlDsa.X86_64.Arith.montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))))) _
    intro i hi
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_caddV _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_psubd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_csubV _ hi]
    exact (VG.Proof.MlDsa.X86_64.Arith.bflyD (hx i hi) (VG.Proof.MlDsa.X86_64.Arith.mulZ (hy i hi) (hz i hi) (VG.Proof.MlDsa.X86_64.Arith.dword_montV ho (VG.Proof.MlDsa.X86_64.Arith.prod_lt hy hz) hi))).2

theorem vibfly_ok {s : State} (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s) {x y ζ : Nat → Zq} (hx : VG.Proof.MlDsa.X86_64.Arith.DLanes (s.xmm .xmm0) x)
    (hy : VG.Proof.MlDsa.X86_64.Arith.DLanes (s.xmm .xmm1) y) (hz : VG.Proof.MlDsa.X86_64.Arith.ZLanes (s.xmm .xmm13) ζ) (ho : VG.Proof.MlDsa.X86_64.Arith.ZOdd (s.xmm .xmm13) (s.xmm .xmm12)) :
    WP isa (.block vibfly) s fun s' => VG.Proof.MlDsa.X86_64.Arith.DLanes (s'.xmm .xmm0) (fun i => x i + y i) ∧
      VG.Proof.MlDsa.X86_64.Arith.DLanes (s'.xmm .xmm3) (fun i => ζ i * (y i - x i)) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' := by
  simp only [vibfly, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [VG.Proof.MlDsa.X86_64.Arith.eval_movdqa]
  rw [hc.q, hc.qinv]
  have e : ∀ i < 4, dword (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) VG.Proof.MlDsa.X86_64.Arith.qV) i =
      dword (s.xmm .xmm1) i - dword (s.xmm .xmm0) i + VG.Proof.MlDsa.X86_64.Arith.qB := fun i hi => by
    rw [dword_paddd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_psubd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_qV hi]
  have hb : ∀ i < 4, (dword (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) VG.Proof.MlDsa.X86_64.Arith.qV) i).toNat *
      (dword (s.xmm .xmm13) i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [e i hi, VG.Proof.MlDsa.X86_64.Arith.subq_toNat (by rw [hx i hi]; exact val_lt _) (by rw [hy i hi]; exact val_lt _), hx i hi, hy i hi,
      hz i hi]
    exact VG.Proof.MlDsa.X86_64.Arith.subq_mul_lt (val_lt (x i)) (val_lt (y i)) (Nat.mod_lt _ (by decide))
  refine ⟨?_, ?_, by xonly⟩
  · change VG.Proof.MlDsa.X86_64.Arith.DLanes (VG.Proof.MlDsa.X86_64.Arith.csubV (XBinOp.eval .paddd (s.xmm .xmm0) (s.xmm .xmm1))) _
    intro i hi
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_csubV _ hi, dword_paddd _ _ hi, VG.Proof.MlDsa.X86_64.Arith.addD_toNat (by rw [hx i hi]; exact val_lt _)
      (by rw [hy i hi]; exact val_lt _), hx i hi, hy i hi, val_add]
  · change VG.Proof.MlDsa.X86_64.Arith.DLanes (VG.Proof.MlDsa.X86_64.Arith.csubV (VG.Proof.MlDsa.X86_64.Arith.montV (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) VG.Proof.MlDsa.X86_64.Arith.qV)
      (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_csubV _ hi]
    exact (VG.Proof.MlDsa.X86_64.Arith.ibflyD (hx i hi) (hy i hi) (hz i hi) (by rw [VG.Proof.MlDsa.X86_64.Arith.dword_montV ho hb hi, e i hi])).2

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic`. -/
section

/-!
# ML-DSA on x86-64: reduction modulo `q`, and the contracts

It uses the symbolic execution of ML-KEM's x86-64 proofs (`xrun`, `Keep`,
`WP.keep`, the counted loops, `Proof/MlKem/X86_64/Wp.lean`), which are about
the ISA, not ML-KEM.

* `csubQ` leaves `csubD v` of `v`, `v mod q` for `v < 2q` (`csubD_toNat`);
* `reduce` leaves `redD x` in `r10` of any `x` in `rax`, which is `x mod q`
  (`reduce_ok`, `redD_toNat`): `barrett` of `Arith/Zq.lean` then `csubQ`;
* for each function, a contract with the facts of its shared contract
  (`Spec/MlDsa/Poly.lean`) spelled out for x86-64: the arguments in their
  registers, the permitted regions, their disjointness, and the
  postcondition. The proofs are written against these, and
  `Verified.of_correct` moves them to the shared contracts, which imply them
  (`mldsa_implies`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of wp_countdown wp_counted ifp ifn
  toNat_setWidth64 toNat_setWidth32_64 read_zero)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## Immediates -/

theorem qImm_toNat : qImm.toNat = 8380417 := rfl

theorem sxQD : BitVec.signExtend 64 qImm = 8380417 := by decide

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ea_atD (s : State) (b : Reg) (d : Nat) : s.ea (VG.Impl.MlDsa.X86_64.Arith.at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.MlDsa.X86_64.Arith.at_]
  congr 1

/-- `xrun` (`Proof/MlKem/X86_64/Wp.lean`) for this code's memory operands
and immediates. -/
syntax "xrund" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| xrund) => `(tactic| xrund [])
  | `(tactic| xrund [$ls,*]) => `(tactic| xrun [ea_atD, sxQD, $ls,*])

/-! ## `csubQ` -/

/-- What `csubQ` leaves of `v`. -/
def csubD (v : BitVec 32) : BitVec 32 :=
  v - qImm + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < qImm.toNat))) &&& qImm)

theorem csubD_toNat (v : BitVec 32) : (VG.Proof.MlDsa.X86_64.Arith.csubD v).toNat = condSub v.toNat := by
  unfold VG.Proof.MlDsa.X86_64.Arith.csubD condSub
  rw [VG.Proof.MlDsa.X86_64.Arith.qImm_toNat]
  by_cases h : 8380417 ≤ v.toNat
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < 8380417))) &&& qImm) = 0 := by
      rw [decide_eq_false (by omega)]; decide
    rw [e, ifp (by rw [q_eq]; exact h)]
    unfold qImm
    rw [q_eq]
    bv_omega
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < 8380417))) &&& qImm) = qImm := by
      rw [decide_eq_true (by omega)]; decide
    rw [e, ifn (by rw [q_eq]; exact h)]
    unfold qImm
    bv_omega

theorem csubD_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Arith.csubD (a + b)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add]; rw [q_eq] at *; omega
  rw [VG.Proof.MlDsa.X86_64.Arith.csubD_toNat, e]

theorem csubD_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Arith.csubD (a + qImm - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a + qImm - b).toNat = a.toNat + q - b.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.MlDsa.X86_64.Arith.qImm_toNat]; rw [q_eq] at *; omega
  rw [VG.Proof.MlDsa.X86_64.Arith.csubD_toNat, e]

/-- `csubQ` after adding two words of values `x` and `y`. -/
theorem csubD_add_val {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (VG.Proof.MlDsa.X86_64.Arith.csubD (a + b)).toNat = (x + y).val := by
  rw [VG.Proof.MlDsa.X86_64.Arith.csubD_add (by rw [ha]; exact x.isLt) (by rw [hb]; exact y.isLt), ha, hb, val_add]

/-- `csubQ` after subtracting a word of value `y` from one of value `x`. -/
theorem csubD_sub_val {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (VG.Proof.MlDsa.X86_64.Arith.csubD (a + qImm - b)).toNat = (x - y).val := by
  rw [VG.Proof.MlDsa.X86_64.Arith.csubD_sub (by rw [ha]; exact x.isLt) (by rw [hb]; exact y.isLt), ha, hb, val_sub]

/-! ## `reduce` -/

/-- What `reduce` leaves in `r10`, of `x`. -/
def redD (x : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (VG.Proof.MlDsa.X86_64.Arith.csubD (BitVec.setWidth 32 (x - BitVec.ofNat 64
    ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat * BitVec.toNat (8380417 : BitVec 64)))))

theorem redD_toNat (x : BitVec 64) : (VG.Proof.MlDsa.X86_64.Arith.redD x).toNat = x.toNat % q := by
  have hx := x.isLt
  have hb := barrett_bounds hx
  have e1 : (BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat = barrettQuot x.toNat := by
    rw [BitVec.toNat_ofNat, show barrettImm.toNat = barrettM from rfl, Nat.mod_eq_of_lt]; rfl
    unfold barrettM; omega
  have e2 : (BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat *
      BitVec.toNat (8380417 : BitVec 64))).toNat = barrettQuot x.toNat * q := by
    rw [e1, show BitVec.toNat (8380417 : BitVec 64) = q from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have e3 : (x - BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat *
      BitVec.toNat (8380417 : BitVec 64))).toNat = barrett x.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e2]; exact hb.1), e2]; rfl
  have hl : barrett x.toNat < 2 * q := barrett_lt hx
  have e4 := toNat_setWidth32_64 (show (x - BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat /
    2 ^ 64)).toNat * BitVec.toNat (8380417 : BitVec 64))).toNat < 2 ^ 32 by rw [e3]; rw [q_eq] at hl; omega)
  rw [e3] at e4
  rw [VG.Proof.MlDsa.X86_64.Arith.redD, toNat_setWidth64, VG.Proof.MlDsa.X86_64.Arith.csubD_toNat, e4, reduce_barrett hx]

/-- The low half of `redD x`, whose value is `x mod q`. -/
theorem redD32_toNat (x : BitVec 64) : (BitVec.setWidth 32 (VG.Proof.MlDsa.X86_64.Arith.redD x)).toNat = x.toNat % q := by
  have h := VG.Proof.MlDsa.X86_64.Arith.redD_toNat x
  have : x.toNat % q < q := Nat.mod_lt _ (by decide)
  rw [toNat_setWidth32_64 (by rw [h]; exact Nat.lt_of_lt_of_le this (by decide)), h]

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' => (s'.gpr .r10 = VG.Proof.MlDsa.X86_64.Arith.redD (s.gpr .rax) ∧ s'.mem = s.mem) ∧
      Keep [.rax, .rdx, .r10, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold reduce csubQ
  xrund [List.cons_append, List.nil_append, VG.Proof.MlDsa.X86_64.Arith.csubD, VG.Proof.MlDsa.X86_64.Arith.redD]

/-- The product of a word and `r`, as `mul` leaves it. -/
abbrev prodW (a : BitVec 32) (r : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * r.toNat)

/-- The product of a word of value `x` and a register of value `z`, reduced:
the value of `z · x`. -/
theorem redD_prodW {u : BitVec 32} {x z : Zq} (hu : u.toNat = x.val) :
    (BitVec.setWidth 32 (VG.Proof.MlDsa.X86_64.Arith.redD (VG.Proof.MlDsa.X86_64.Arith.prodW u (BitVec.ofNat 64 z.val)))).toNat = (z * x).val := by
  have hz := val_lt z
  have hx := val_lt x
  have e : (VG.Proof.MlDsa.X86_64.Arith.prodW u (BitVec.ofNat 64 z.val)).toNat = x.val * z.val := by
    rw [VG.Proof.MlDsa.X86_64.Arith.prodW, BitVec.toNat_ofNat, toNat_setWidth64, hu, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := z.val) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mul_lt_q2 hx hz) (by decide))
  rw [VG.Proof.MlDsa.X86_64.Arith.redD32_toNat, e, val_mul, Nat.mul_comm]

/-! ## The contracts -/

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mldsa_ntt(f = rdi, scratch = rsi)` and `vg_mldsa_inv_ntt`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi), VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)] ∧ (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)) ∧
    (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)) ∧ (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mldsa_add(f = rdi, g = rsi)` and `vg_mldsa_sub(f = rdi, g = rsi)`:
`f` becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)] ∧ s.wr = [VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)] ∧
    (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)) ∧ (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)) ∧
    (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mldsa_multiply_ntt(h = rdi, f = rsi, g = rdx)` and
`vg_mldsa_multiply_add_ntt`: `h` becomes `t h f g`, if `hPre` of `h` (for
`vg_mldsa_multiply_add_ntt`, that it is reduced). -/
def mulK (t : Poly → Poly → Poly → Poly) (hPre : Mem → Addr → Prop) : Contract isa where
  pre s :=
    s.rd = [VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi), VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdx)] ∧ s.wr = [VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)] ∧
    (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)) ∧ (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdx)) ∧
    (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdi)) ∧ (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rsi)) ∧
    (VG.Proof.MlDsa.X86_64.Arith.retR s).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR (s.gpr .rdx)) ∧ hPre s.mem (s.gpr .rdi) ∧
    Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx)
  post s s' := PolyIs s'.mem (s.gpr .rdi)
    (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Satisfiability -/

/-- In memory of zeros, every polynomial is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, read_zero]
  decide

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "mldsa_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mldsa_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table`. -/
section

/-!
# ML-DSA on x86-64: tables of constants in the working space

A table of `u32`s in the working space (`Tab`), which writes elsewhere keep
(`Tab.frame`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (coeffAt)

/-- The first `n` entries of the table `t` are the `u32`s at `p`. -/
def Tab (t : Nat → Nat) (m : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ k < n, coeffAt m p k = BitVec.ofNat 32 (t k)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {p : Addr} {n : Nat} (h : VG.Proof.MlDsa.X86_64.Arith.Tab t m p n) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.X86_64.Arith.pR p).Disjoint r) (hn : n ≤ 256) : VG.Proof.MlDsa.X86_64.Arith.Tab t m' p n :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < 256 by omega)]; exact h k hk

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem`. -/
section

/-!
# ML-DSA on x86-64: four coefficients at a time in memory

16-byte loads of four coefficients of a stored polynomial (`dlanes_load`) and
stores of them (`polyIs_write2`), and the table of the zetas in Montgomery
form (`Tab zmTab`), from which `vzeta` loads the zetas of up to four blocks
(`vzeta_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly xmm_setXmm ifp ifn sel sel_lt add_ofNat_zero)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)

theorem dlanes_load {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat} (hj : j + 4 ≤ 256) :
    VG.Proof.MlDsa.X86_64.Arith.DLanes (m.readW (coeffAddr p j) 128) (fun e => F[j + e]!) := fun e he => by
  rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq]
  exact polyIs_toNat h (by rw [n_eq]; omega)

/-- Coefficient `i` after storing `x` at coefficient `j`. -/
theorem coeffAt_write128 (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i = if j ≤ i ∧ i < j + 4 then dword x (i - j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega]]
    exact readW_writeW128 _ _ _ (by omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Two vectors stored into a polynomial, with the lanes `a` and `b`. -/
theorem polyIs_write2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) (hsep : j + 4 ≤ j' ∨ j' + 4 ≤ j) {x y : BitVec 128}
    {a b : Nat → Zq} (hx : VG.Proof.MlDsa.X86_64.Arith.DLanes x a) (hy : VG.Proof.MlDsa.X86_64.Arith.DLanes y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 4 then a (i - j)
      else if j' ≤ i ∧ i < j' + 4 then b (i - j') else P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) p R := polyIs_of_toNat fun i hi => by
  rw [n_eq] at hi
  rw [VG.Proof.MlDsa.X86_64.Arith.coeffAt_write128 _ _ hj' _ hi, VG.Proof.MlDsa.X86_64.Arith.coeffAt_write128 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 4
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact hy _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact hx _ (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact polyIs_toNat hP (by rw [n_eq]; exact hi)

theorem pR_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) : (VG.Proof.MlDsa.X86_64.Arith.pR p).Contains (coeffAddr p j) 16 :=
  Offset.contains_base p (by omega) (by omega)

theorem frame_write2 {m m' : Mem} {p : Addr} (hf : Frame [VG.Proof.MlDsa.X86_64.Arith.pR p] m m') {j j' : Nat} (hj : j + 4 ≤ 256)
    (hj' : j' + 4 ≤ 256) (x y : BitVec 128) :
    Frame [VG.Proof.MlDsa.X86_64.Arith.pR p] m ((m'.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (VG.Proof.MlDsa.X86_64.Arith.pR_contains p hj)).writeW (List.mem_singleton_self _) y
    (VG.Proof.MlDsa.X86_64.Arith.pR_contains p hj')

/-! ## The table of zetas -/

theorem zmTab_lt (k : Nat) : zmTab k < q := Nat.mod_lt _ (by decide)

theorem zmTab_eq (k : Nat) : zmTab k = (zetas k).val * 2 ^ 32 % q := by
  rw [zmTab, ← zetaNat_eq, zetaNat, Nat.mod_mul_mod]

/-- The zeta at index `k` of the table. -/
theorem tab_zeta {m : Mem} {zP : Addr} (ht : VG.Proof.MlDsa.X86_64.Arith.Tab zmTab m zP 256) {k : Nat} (hk : k < 256) :
    (m.readW (coeffAddr zP k) 32).toNat = (zetas k).val * 2 ^ 32 % q := by
  rw [← coeffAt_eq, ht k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.MlDsa.X86_64.Arith.zmTab_lt k) (by decide)),
    VG.Proof.MlDsa.X86_64.Arith.zmTab_eq]

theorem dword_shufDwords_sel (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (shufDwords a o) i = dword a (sel o i) := dword_shufDwords a o hi

theorem vzeta_ok (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 256) {s : State}
    (h8 : s.gpr .r8 = coeffAddr zP k) (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16)
    (ht : VG.Proof.MlDsa.X86_64.Arith.Tab zmTab s.mem zP 256) :
    WP isa (.block (vzeta o)) s fun s' =>
      VG.Proof.MlDsa.X86_64.Arith.ZLanes (s'.xmm .xmm13) (fun i => zetas (k + sel o i)) ∧ VG.Proof.MlDsa.X86_64.Arith.ZOdd (s'.xmm .xmm13) (s'.xmm .xmm12) ∧
        XOnly [.xmm13, .xmm12] s s' := by
  simp only [vzeta]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128, VG.Proof.MlDsa.X86_64.Arith.ea_atD,
    add_ofNat_zero, h8, hin, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun j hj => ?_, by xonly⟩
  · simp only [xmm_setXmm, ite_true, ite_false, reduceCtorEq]
    have hs := sel_lt o i
    rw [VG.Proof.MlDsa.X86_64.Arith.dword_shufDwords_sel _ _ hi, dword_readW _ _ hs, coeffAddr_add]
    exact VG.Proof.MlDsa.X86_64.Arith.tab_zeta ht (hk i hi)
  · simp only [xmm_setXmm, ite_true, ite_false, reduceCtorEq]
    rw [dword_shufDwords _ _ (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay`. -/
section

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len ≥ 4`

For any butterfly code `bf` that does what `op` does to the doublewords of two
registers (`VBflyOk`), and any block of the specification whose butterflies do
`op` (`BlkOk`): four butterflies of a block (`vstep`), the `len / 4` of them
of a block (`vblock_ok`), and the `128 / len` blocks of a layer (`vlay_ok`),
on the polynomial at `fP`, with the zetas from the table at `sP`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly xmm_setXmm ifp ifn sel sel_lt sel_zero add_ofNat_zero Keep wp_countdown
  GOnly wp_rcxLoop sx1 sx16)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)

/-- Runs a block of general-purpose and SSE instructions. -/
syntax "vrund" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vrund) => `(tactic| vrund [])
  | `(tactic| vrund [$ls,*]) => `(tactic| vrunm [ea_atD, $ls,*])

/-- `GOnly` of a chain of `setReg` and `setFlags`. -/
macro "gonlyd" : tactic => `(tactic| exact ⟨⟨fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false], rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem gonly_vconsts {rs : List Reg} {s s' : State} (h : GOnly rs s s') (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s) : VG.Proof.MlDsa.X86_64.Arith.VConsts s' :=
  ⟨by rw [h.xmm]; exact hc.q, by rw [h.xmm]; exact hc.qinv⟩

/-- The code `bf` of four butterflies does what `op` does to each pair of
doublewords of `xmm0` and `xmm1`, with the zetas in `xmm13` (and `xmm12`),
leaving the results in `xmm0` and `xmm3`. -/
def VBflyOk (bf : List Instr) (op : Zq → Zq → Zq → Zq × Zq) : Prop :=
  ∀ s : State, VG.Proof.MlDsa.X86_64.Arith.VConsts s → ∀ x y ζ : Nat → Zq, VG.Proof.MlDsa.X86_64.Arith.DLanes (s.xmm .xmm0) x → VG.Proof.MlDsa.X86_64.Arith.DLanes (s.xmm .xmm1) y →
    VG.Proof.MlDsa.X86_64.Arith.ZLanes (s.xmm .xmm13) ζ → VG.Proof.MlDsa.X86_64.Arith.ZOdd (s.xmm .xmm13) (s.xmm .xmm12) →
    WP isa (.block bf) s fun s' => VG.Proof.MlDsa.X86_64.Arith.DLanes (s'.xmm .xmm0) (fun i => (op (x i) (y i) (ζ i)).1) ∧
      VG.Proof.MlDsa.X86_64.Arith.DLanes (s'.xmm .xmm3) (fun i => (op (x i) (y i) (ζ i)).2) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s'

theorem vbfly_spec : VG.Proof.MlDsa.X86_64.Arith.VBflyOk vbfly (fun x y z => (x + z * y, x - z * y)) :=
  fun _ hc _ _ _ hx hy hz ho => VG.Proof.MlDsa.X86_64.Arith.vbfly_ok hc hx hy hz ho

theorem vibfly_spec : VG.Proof.MlDsa.X86_64.Arith.VBflyOk vibfly (fun x y z => (x + y, z * (y - x))) :=
  fun _ hc _ _ _ hx hy hz ho => VG.Proof.MlDsa.X86_64.Arith.vibfly_ok hc hx hy hz ho

/-! ## A block -/

theorem f_in {rs : List Region} {fP : Addr} (hw : VG.Proof.MlDsa.X86_64.Arith.pR fP ∈ rs) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions rs (coeffAddr fP j) 16 :=
  ⟨_, hw, VG.Proof.MlDsa.X86_64.Arith.pR_contains fP hj⟩

theorem tab_in {rs : List Region} {sP : Addr} (hw : VG.Proof.MlDsa.X86_64.Arith.pR sP ∈ rs) {k : Nat} (hk : k + 4 ≤ 256) :
    InRegions rs (coeffAddr sP k) 16 :=
  ⟨_, hw, VG.Proof.MlDsa.X86_64.Arith.pR_contains sP hk⟩

/-- The facts a block keeps. -/
structure BInv (fP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [VG.Proof.MlDsa.X86_64.Arith.pR fP] s₀.mem s.mem
  consts : VG.Proof.MlDsa.X86_64.Arith.VConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInv.trans {fP : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.X86_64.Arith.BInv fP s₁ s₂) (h₂ : VG.Proof.MlDsa.X86_64.Arith.BInv fP s₂ s₃) : VG.Proof.MlDsa.X86_64.Arith.BInv fP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

/-! ## Four butterflies -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VG.Proof.MlDsa.X86_64.Arith.VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- The body of the loop over the vectors of a block. -/
abbrev vbody (bf : List Instr) (len : Nat) : List Instr :=
  [.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx (4 * len))] ++ bf ++
    [.movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx (4 * len)) .xmm3, .alu .add .rdx (.imm 16)] ++
    [.alu .sub .rcx (.imm 1)]

theorem vstep {fP : Addr} {len st u k : Nat} (hl : 0 < len) (hs : st + 2 * len ≤ 256) (hu : 4 * u + 4 ≤ len)
    {G : Poly} {s : State} (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s) (hz : VG.Proof.MlDsa.X86_64.Arith.ZLanes (s.xmm .xmm13) (fun _ => zetas k))
    (ho : VG.Proof.MlDsa.X86_64.Arith.ZOdd (s.xmm .xmm13) (s.xmm .xmm12))
    (hdx : s.gpr .rdx = coeffAddr fP (st + 4 * u)) (hS : PolyIs s.mem fP (blk G len k st (4 * u)))
    (hw : VG.Proof.MlDsa.X86_64.Arith.pR fP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.Arith.vbody bf len)) s fun s' =>
      PolyIs s'.mem fP (blk G len k st (4 * (u + 1))) ∧ s'.gpr .rdx = coeffAddr fP (st + 4 * (u + 1)) ∧
        Frame [VG.Proof.MlDsa.X86_64.Arith.pR fP] s.mem s'.mem ∧ VG.Proof.MlDsa.X86_64.Arith.VConsts s' ∧ s'.xmm .xmm13 = s.xmm .xmm13 ∧
        s'.xmm .xmm12 = s.xmm .xmm12 ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : st + 4 * u + 4 ≤ 256 := by omega
  have j1 : st + 4 * u + len + 4 ≤ 256 := by omega
  have a1 : coeffAddr fP (st + 4 * u) + BitVec.ofNat 64 (4 * len) = coeffAddr fP (st + 4 * u + len) :=
    coeffAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 4 * u)) 16 := VG.Proof.MlDsa.X86_64.Arith.f_in (List.mem_append_right _ hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 4 * u + len)) 16 := VG.Proof.MlDsa.X86_64.Arith.f_in (List.mem_append_right _ hw) j1
  have w0 := VG.Proof.MlDsa.X86_64.Arith.f_in hw j0
  have w1 := VG.Proof.MlDsa.X86_64.Arith.f_in hw j1
  rw [VG.Proof.MlDsa.X86_64.Arith.vbody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  vrund [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  have hx := VG.Proof.MlDsa.X86_64.Arith.dlanes_load hS j0
  have hy := VG.Proof.MlDsa.X86_64.Arith.dlanes_load hS j1
  refine WP.mono (hbf _ ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _)
    (fun e => (blk G len k st (4 * u))[st + 4 * u + e]!) (fun e => (blk G len k st (4 * u))[st + 4 * u + len + e]!)
    (fun _ => zetas k) (by rw [xmm_setXmm, xmm_setXmm]; exact hx) (by rw [xmm_setXmm]; exact hy)
    (by rw [xmm_setXmm, xmm_setXmm]; exact hz) (by rw [xmm_setXmm, xmm_setXmm, xmm_setXmm, xmm_setXmm]; exact ho))
    fun s2 ⟨l0, l3, o2⟩ => ?_
  have c2 := VG.Proof.MlDsa.X86_64.Arith.xonly_vconsts o2 ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _) (by decide)
    (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨o2.rd, o2.wr⟩
  have x2 : s2.mxcsr = s.mxcsr := o2.mxcsr
  have z2 : s2.xmm .xmm13 = s.xmm .xmm13 := by rw [o2.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  have z2' : s2.xmm .xmm12 = s.xmm .xmm12 := by rw [o2.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  vrund [g2, m2, e2.1, e2.2, hdx, a1, w0, w1, x2]
  refine ⟨?_, ?_, ?_, ⟨c2.q, c2.qinv⟩, z2, z2', ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · refine VG.Proof.MlDsa.X86_64.Arith.polyIs_write2 hS j0 j1 (by omega) l0 l3 fun i hi => ?_
    rw [show 4 * (u + 1) = 4 * u + 4 by omega, hblk.add, hblk.get _ _ _ _ _ hl (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    by_cases c1 : st + 4 * u ≤ i ∧ i < st + 4 * u + 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c1), ite_eq_left_of_eq_true _ _ (eq_true c1),
        show st + 4 * u + (i - (st + 4 * u)) = i by omega,
        show st + 4 * u + len + (i - (st + 4 * u)) = i + len by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c1)]
      by_cases c2 : st + 4 * u + len ≤ i ∧ i < st + 4 * u + len + 4
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c2), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          show st + 4 * u + (i - (st + 4 * u + len)) = i - len by omega,
          show st + 4 * u + len + (i - (st + 4 * u + len)) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add,
      show st + 4 * u + 4 = st + 4 * (u + 1) by omega]
  · exact VG.Proof.MlDsa.X86_64.Arith.frame_write2 (Frame.refl _ _) j0 j1 _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-- The code of a block of a layer with `len ≥ 4`. -/
abbrev vblk (bf : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (vzeta 0 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (VG.Impl.MlKem.X86_64.rcxLoop (len / 4) ([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0),
        .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx (4 * len))] ++
        bf ++ [.movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlDsa.X86_64.Arith.at_ .rdx (4 * len)) .xmm3,
          .alu .add .rdx (.imm 16)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rax (.imm 1)]))

theorem vblock_ok {fP sP : Addr} {len st kz : Nat} (h4 : 4 ≤ len) (hl4 : len % 4 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz + 4 ≤ 256) (dz : BitVec 32) {G : Poly} {s : State} (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s)
    (hdx : s.gpr .rdx = coeffAddr fP st) (h8r : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP G)
    (hT : VG.Proof.MlDsa.X86_64.Arith.Tab zmTab s.mem sP 256) (hwf : VG.Proof.MlDsa.X86_64.Arith.pR fP ∈ s.wr) (hw : VG.Proof.MlDsa.X86_64.Arith.pR sP ∈ s.wr) :
    WP isa (VG.Proof.MlDsa.X86_64.Arith.vblk bf len dz) s fun s' => PolyIs s'.mem fP (blk G len kz st len) ∧
      s'.gpr .rdx = coeffAddr fP (st + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ VG.Proof.MlDsa.X86_64.Arith.BInv fP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.vzeta_ok 0 (k := kz) (fun j _ => by rw [sel_zero]; omega) h8r
    (VG.Proof.MlDsa.X86_64.Arith.tab_in (List.mem_append_right _ hw) hkz) hT) fun s1 ⟨z1, zo1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      GOnly [.r8] s1 s2)
    (by vrund [g1]; gonlyd)
    fun s2 ⟨h82, o2⟩ => ?_
  have c2 := VG.Proof.MlDsa.X86_64.Arith.gonly_vconsts o2 (VG.Proof.MlDsa.X86_64.Arith.xonly_vconsts o1 hc (by decide) (by decide))
  have z2 : VG.Proof.MlDsa.X86_64.Arith.ZLanes (s2.xmm .xmm13) (fun _ => zetas kz) := by
    rw [o2.xmm]; intro i hi; rw [z1 i hi]; dsimp only; rw [sel_zero, Nat.add_zero]
  have zo2 : VG.Proof.MlDsa.X86_64.Arith.ZOdd (s2.xmm .xmm13) (s2.xmm .xmm12) := by rw [o2.xmm]; exact zo1
  have dx2 : s2.gpr .rdx = coeffAddr fP st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : VG.Proof.MlDsa.X86_64.Arith.pR fP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hwf
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoop (N := len / 4) (by omega) (by omega)
    (fun u w => PolyIs w.mem fP (blk G len kz st (4 * u)) ∧ w.gpr .rdx = coeffAddr fP (st + 4 * u) ∧
      VG.Proof.MlDsa.X86_64.Arith.VConsts w ∧ w.xmm .xmm13 = s2.xmm .xmm13 ∧ w.xmm .xmm12 = s2.xmm .xmm12 ∧ Keep [.rcx, .rdx] s2 w ∧
      Frame [VG.Proof.MlDsa.X86_64.Arith.pR fP] s2.mem w.mem ∧ w.mxcsr = s2.mxcsr)
    (fun w o hc => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      VG.Proof.MlDsa.X86_64.Arith.gonly_vconsts o c2, by rw [o.xmm], by rw [o.xmm], o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _,
      o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Arith.vstep hbf hblk (by omega) hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl4); omega) hc' (by rw [hz']; exact z2)
        (by rw [hz', hzo']; exact zo2) hdx' hS' (by rw [hk'.2.2]; exact hw2))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', by rw [hz'', hz'], by rw [hzo'', hzo'], (hk'.trans hk'').mono (by simp),
          hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩)) fun w ⟨hS3, hdx3, hc3, _, _, hk3, hf3, hx3⟩ => ?_)
  rw [show 4 * (len / 4) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl4)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [hk3.gpr (by decide), h82]
  vrund [hdx3, VG.Proof.MlDsa.X86_64.Arith.sx_ofNat (show 4 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [coeffAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hc3.q,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hc3.qinv⟩,
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

/-! ## A layer -/

theorem vlay_ok {fP sP : Addr} {len k : Nat} (hlen : len ∈ [4, 8, 16, 32, 64, 128]) (dz : BitVec 32)
    (zi : Nat → Nat) (hz0 : zi 0 = k) (hzi : ∀ c < 128 / len, zi c + 4 ≤ 256)
    (hstep : ∀ c < 128 / len, coeffAddr sP (zi c) + BitVec.signExtend 64 dz = coeffAddr sP (zi (c + 1)))
    {F : Poly} {s : State} (hc : VG.Proof.MlDsa.X86_64.Arith.VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : VG.Proof.MlDsa.X86_64.Arith.Tab zmTab s.mem sP 256) (hwf : VG.Proof.MlDsa.X86_64.Arith.pR fP ∈ s.wr) (hw : VG.Proof.MlDsa.X86_64.Arith.pR sP ∈ s.wr)
    (hd : (VG.Proof.MlDsa.X86_64.Arith.pR sP).Disjoint (VG.Proof.MlDsa.X86_64.Arith.pR fP)) :
    WP isa (vlay bf len k dz) s fun s' => PolyIs s'.mem fP (layF blk F len zi (128 / len)) ∧
      VG.Proof.MlDsa.X86_64.Arith.BInv fP s s' := by
  have hl : 4 ≤ len ∧ len % 4 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h4, hl4, hl128, hcov, hpos, h32⟩ := hl
  have hk : k + 4 ≤ 256 := hz0 ▸ hzi 0 hpos
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w)
    (by
      simp only [leaR]
      vrund [VG.Proof.MlDsa.X86_64.Arith.sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi]
      refine ⟨?_, by gonlyd⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o⟩ => ?_)
  have hwf' : VG.Proof.MlDsa.X86_64.Arith.pR fP ∈ w.wr := by rw [o.keep.2.2]; exact hwf
  have hw' : VG.Proof.MlDsa.X86_64.Arith.pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => PolyIs u.mem fP (layF blk F len zi c) ∧ u.gpr .rdx = coeffAddr fP (2 * len * c) ∧
      u.gpr .r8 = coeffAddr sP (zi c) ∧ VG.Proof.MlDsa.X86_64.Arith.BInv fP w u ∧ VG.Proof.MlDsa.X86_64.Arith.Tab zmTab u.mem sP 256)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, hz0], ⟨Keep.refl _ _, Frame.refl _ _, VG.Proof.MlDsa.X86_64.Arith.gonly_vconsts o hc, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.vblock_ok hbf hblk h4 hl4 hl128 hs (hzi c hc) dz hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hwf') (by rw [hb'.keep.2.2]; exact hw'))
    fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', h8', hstep c hc], hb'.trans hb'',
        hT'.frame hb''.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)⟩, hax'', hzf''⟩

end

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_add` and `vg_mldsa_sub`

Each iteration of the loop stores four coefficients to `f` (`addBody_ok`,
`subBody_ok`), each `csubL` of the sum (`caddL` of the difference), whose
value is `addD_toNat` (`subD_toNat`); the loop leaves `f` with all 256
(`AddSub.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of ifp ifn ptr_step GOnly wp_rcxLoop xmm_setXmm
  add_ofNat_zero)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## Four coefficients -/

/-- What an iteration of `add` stores. -/
def addV (x y : BitVec 128) : BitVec 128 := VG.Proof.MlDsa.X86_64.Arith.csubV (XBinOp.eval .paddd x y)

/-- What an iteration of `sub` stores. -/
def subV (x y : BitVec 128) : BitVec 128 := VG.Proof.MlDsa.X86_64.Arith.caddV (XBinOp.eval .psubd x y)

theorem dword_addV (x y : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (VG.Proof.MlDsa.X86_64.Arith.addV x y) i = VG.Proof.MlDsa.X86_64.Arith.csubL (dword x i + dword y i) := by
  rw [VG.Proof.MlDsa.X86_64.Arith.addV, VG.Proof.MlDsa.X86_64.Arith.dword_csubV _ hi, dword_paddd _ _ hi]

theorem dword_subV (x y : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (VG.Proof.MlDsa.X86_64.Arith.subV x y) i = VG.Proof.MlDsa.X86_64.Arith.caddL (dword x i - dword y i) := by
  rw [VG.Proof.MlDsa.X86_64.Arith.subV, VG.Proof.MlDsa.X86_64.Arith.dword_caddV _ hi, VG.Proof.MlDsa.X86_64.Arith.dword_psubd _ _ hi]

/-- The body of `add` or `sub`: the store of `F x y` of the vectors at `rdi`
and `rsi`, and the counts. -/
theorem accBody_ok {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
    (hF : ∀ (s : State), s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV →
      WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
        s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
          s'.wr = s.wr ∧ s'.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV)
    (s : State) (hq : s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) (h3 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block (([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] : List Instr) ++
        ((xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))))) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi) (F (s.mem.readW (s.gpr .rdi) 128) (s.mem.readW (s.gpr .rsi) 128)) ∧
        s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV ∧
        Keep [.rdi, .rsi, .rcx] s s' := by
  rw [WP.block_append_iff]
  vrund [h1, h2]
  rw [show Instr.xop (.bin op .xmm0 .xmm1) :: (fix ++ (accTail ++ [.alu .sub .rcx (.imm 1)])) =
    (xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr)) from rfl,
    WP.block_append_iff]
  refine WP.mono (hF _ (by simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hq))
    fun s2 ⟨h0, g2, m2, r2, w2, q2⟩ => ?_
  simp only [accTail]
  vrund [g2, m2, r2, w2, h3, h0, q2]
  refine ⟨fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

theorem addFix_ok (s : State) (hq : s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV) :
    WP isa (.block (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = VG.Proof.MlDsa.X86_64.Arith.addV (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV := by
  simp only [vcsub, vcadd, xmov, xb]
  vrun [VG.Proof.MlDsa.X86_64.Arith.eval_movdqa]
  rw [hq]
  exact ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

theorem subFix_ok (s : State) (hq : s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV) :
    WP isa (.block (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = VG.Proof.MlDsa.X86_64.Arith.subV (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV := by
  simp only [vcadd, xmov, xb]
  vrun [VG.Proof.MlDsa.X86_64.Arith.eval_movdqa]
  rw [hq]
  exact ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

/-! ## The loop -/

namespace AddSub

/-- After `i` vectors, each coefficient before `4i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV
  frame : Frame [VG.Proof.MlDsa.X86_64.Arith.pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 4 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (VG.Proof.MlDsa.X86_64.Arith.accK t).pre s₀)
include hp

/-- An iteration, which stores `F` of the vectors of `f` and `g`, whose
doublewords are `L` of theirs. -/
theorem step {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
    {L : BitVec 32 → BitVec 32 → BitVec 32}
    (hF : ∀ (s : State), s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV →
      WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
        s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
          s'.wr = s.wr ∧ s'.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV)
    (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
    {i : Nat} (hi : i < 64) {s : State}
    (hI : VG.Proof.MlDsa.X86_64.Arith.AddSub.Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] : List Instr) ++
        ((xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Arith.AddSub.Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 4 * i + 4 ≤ 256 := by omega
  have hw : VG.Proof.MlDsa.X86_64.Arith.pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : VG.Proof.MlDsa.X86_64.Arith.pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (4 * i) := by rw [hI.rdi]; congr 2; omega
  have e2 : s.gpr .rsi = coeffAddr (s₀.gpr .rsi) (4 * i) := by rw [hI.rsi]; congr 2; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Arith.accBody_ok hF s hI.q (by rw [e1]; exact VG.Proof.MlDsa.X86_64.Arith.f_in (List.mem_append_right _ hw) j0)
    (by rw [e2]; exact ⟨_, hr, VG.Proof.MlDsa.X86_64.Arith.pR_contains _ j0⟩) (by rw [e1]; exact VG.Proof.MlDsa.X86_64.Arith.f_in hw j0))
    fun s' ⟨hm, hdi, hsi, hcx, hz, hrd, hwr, hq, _⟩ => ⟨?_, hcx, hz⟩
  refine ⟨by rw [hdi, hI.rdi]; exact ptr_step _ i 16, by rw [hsi, hI.rsi]; exact ptr_step _ i 16,
    hrd.trans hI.rd, hwr.trans hI.wr, hq, ?_, fun k hk => ?_⟩
  · rw [hm, e1]; exact hI.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.MlDsa.X86_64.Arith.pR_contains _ j0)
  · rw [hm, e1, VG.Proof.MlDsa.X86_64.Arith.coeffAt_write128 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 4 * (i + 1) by omega), hL _ _ _ (by omega), e2, dword_readW _ _ (by omega),
        dword_readW _ _ (by omega), coeffAddr_add, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq,
        show 4 * i + (k - 4 * i) = k by omega, hI.coeff k hk, ifn (by omega),
        coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) (by rw [n_eq]; exact hk)]
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 4 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]

/-- The whole function, from its precondition. -/
theorem fn_ok {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
    {L : BitVec 32 → BitVec 32 → BitVec 32}
    (hF : ∀ (s : State), s.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV →
      WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
        s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
          s'.wr = s.wr ∧ s'.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV)
    (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
    (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx] (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
      (([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
        accTail))) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
      (([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
        accTail)) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
        (([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
          accTail))) s₀ tr s' ∧ abiPreserved s₀ s' ∧ (VG.Proof.MlDsa.X86_64.Arith.accK t).post s₀ s' := by
  have hw : VG.Proof.MlDsa.X86_64.Arith.pR (s₀.gpr .rdi) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
      (([.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
        accTail))) s₀
      (VG.Proof.MlDsa.X86_64.Arith.AddSub.Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) 64) := by
    refine WP.seq (WP.mono (Q := fun (w : State) => w.xmm .xmm15 = VG.Proof.MlDsa.X86_64.Arith.qV ∧ Keep [.rax] s₀ w ∧ w.mem = s₀.mem)
      (by
        simp only [qPro]
        vrund
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun w ⟨hq, k1, m1⟩ => ?_)
    refine wp_rcxLoop (N := 64) (by decide) (by decide) _ (fun u o _ => ⟨?_, ?_, by rw [o.keep.2.1, k1.2.1],
      by rw [o.keep.2.2, k1.2.2], by rw [o.xmm]; exact hq, by rw [o.mem, m1]; exact Frame.refl _ _,
      fun k _ => by rw [o.mem, m1, ifn (by omega)]⟩) fun i hi u hI => ?_
    · rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero]
    · rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero]
    · rw [show [Instr.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] ++
          (xb op .xmm0 .xmm1 :: fix) ++ accTail ++ [.alu .sub .rcx (.imm 1)] =
          [.movdquLoad .xmm0 (VG.Impl.MlDsa.X86_64.Arith.at_ .rdi 0), .movdquLoad .xmm1 (VG.Impl.MlDsa.X86_64.Arith.at_ .rsi 0)] ++
          ((xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) by
        simp only [List.append_assoc]]
      exact VG.Proof.MlDsa.X86_64.Arith.AddSub.step hp hF hL hi hI
  obtain ⟨tr, s', he, hI, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hI.frame ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    rw [hI.coeff k hk, ifp (by omega)]
    exact hv k hk

end

end AddSub

/-! ## The functions -/

theorem add_correct (s : State) (hs : (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.add).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.add s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.add).post s s' :=
  AddSub.fn_ok hs (op := .paddd) (fix := vcsub .xmm0 .xmm2) (L := fun a b => VG.Proof.MlDsa.X86_64.Arith.csubL (a + b)) VG.Proof.MlDsa.X86_64.Arith.addFix_ok
    (fun x y e he => VG.Proof.MlDsa.X86_64.Arith.dword_addV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [add_get _ _ hk', VG.Proof.MlDsa.X86_64.Arith.addD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_add])
    (by decide +kernel) (by decide +kernel)

theorem sub_correct (s : State) (hs : (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.sub).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.sub s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.sub).post s s' :=
  AddSub.fn_ok hs (op := .psubd) (fix := vcadd .xmm0 .xmm2) (L := fun a b => VG.Proof.MlDsa.X86_64.Arith.caddL (a - b)) VG.Proof.MlDsa.X86_64.Arith.subFix_ok
    (fun x y e he => VG.Proof.MlDsa.X86_64.Arith.dword_subV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [sub_get _ _ hk', VG.Proof.MlDsa.X86_64.Arith.subD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_sub])
    (by decide +kernel) (by decide +kernel)

/-- The pointers and `rsp` are public. -/
def accτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (VG.Proof.MlDsa.X86_64.Arith.accK t).pre s₁) (_ : (VG.Proof.MlDsa.X86_64.Arith.accK t).pre s₂)
    (hp : (VG.Proof.MlDsa.X86_64.Arith.accK t).pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.MlDsa.X86_64.Arith.accτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem add_ct :
    ConstantTime isa (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.add).pre (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.add).pub Impl.MlDsa.X86_64.Arith.add :=
  VG.Taint.constantTime (A := taint) VG.Proof.MlDsa.X86_64.Arith.accτ VG.Proof.MlDsa.X86_64.Arith.acc_agree (by taint_decide)

theorem sub_ct :
    ConstantTime isa (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.sub).pre (VG.Proof.MlDsa.X86_64.Arith.accK Spec.MlDsa.sub).pub Impl.MlDsa.X86_64.Arith.sub :=
  VG.Taint.constantTime (A := taint) VG.Proof.MlDsa.X86_64.Arith.accτ VG.Proof.MlDsa.X86_64.Arith.acc_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def accSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.add (Spec.MlDsa.addContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.add_correct VG.Proof.MlDsa.X86_64.Arith.add_ct (by
    mldsa_implies [Spec.MlDsa.addContract, Spec.MlDsa.accSig, VG.Proof.MlDsa.X86_64.Arith.accK, X86_64.abi, X86_64.argRegs]
      [accSat] using VG.Proof.MlDsa.X86_64.Arith.accSat)

theorem sub_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.sub (Spec.MlDsa.subContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.sub_correct VG.Proof.MlDsa.X86_64.Arith.sub_ct (by
    mldsa_implies [Spec.MlDsa.subContract, Spec.MlDsa.accSig, VG.Proof.MlDsa.X86_64.Arith.accK, X86_64.abi, X86_64.argRegs]
      [accSat] using VG.Proof.MlDsa.X86_64.Arith.accSat)

end VG.Proof.MlDsa.X86_64.Arith

end
