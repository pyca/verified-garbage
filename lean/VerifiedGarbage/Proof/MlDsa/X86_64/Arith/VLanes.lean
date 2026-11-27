module

public import VerifiedGarbage.Proof.MlKem.X86_64.VLanes
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.Arith.Mont
public import VerifiedGarbage.TCB.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.X86_64.VArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `MlDsa.X86_64.Arith.VArith`, which this module and modules that import it used -/

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

@[expose] public section

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
    decide_eq_true (show 0 + j < 64 by omega_using [hj])]
  exact congrArg _ (by omega_using [])

theorem dword_hi (x : BitVec 128) (i : Nat) : dword x (2 * i + 1) = (qword x i).extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 32 + j < 64 by omega_using [hj])]
  exact congrArg _ (by omega_using [])

/-- The low doubleword of a quadword, zero-extended. -/
def lo32 (x : BitVec 64) : BitVec 64 := (x.extractLsb' 0 32).setWidth 64

theorem lo32_toNat (x : BitVec 64) : (lo32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [lo32, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem qword_paddq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .paddq x y) i = qword x i + qword y i := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [reduceXBinOpEval, qword_app0]
  · simp only [reduceXBinOpEval, qword_app1]

theorem qword_pmuludq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pmuludq x y) i = lo32 (qword x i) * lo32 (qword y i) := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [reduceXBinOpEval, qword_app0, lo32, ← dword_lo]
  · simp only [reduceXBinOpEval, qword_app1, lo32, ← dword_lo]

theorem qword_psrlq32 (x : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq x 32) i = qword x i >>> 32 := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [XShiftOp.eval, show ¬ 63 < (32 : BitVec 8).toNat by decide, ite_false, qword_app0]; rfl
  · simp only [XShiftOp.eval, show ¬ 63 < (32 : BitVec 8).toNat by decide, ite_false, qword_app1]; rfl

theorem toNat_lo32_mul (x y : BitVec 64) : (lo32 x * lo32 y).toNat = x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) := by
  rw [BitVec.toNat_mul, lo32_toNat, lo32_toNat]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by decide)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h1 h2) (by decide))

/-! ## Montgomery reduction of a quadword -/

/-- `q` in each doubleword. -/
def qV : BitVec 128 := 0x007FE001007FE001007FE001007FE001#128

/-- `-q⁻¹ mod 2³²` in each doubleword. -/
def qinvV : BitVec 128 := 0xFC7FDFFFFC7FDFFFFC7FDFFFFC7FDFFF#128

theorem lo32_qword_qV {i : Nat} (hi : i < 2) : (lo32 (qword qV i)).toNat = q := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> decide

theorem lo32_qword_qinvV {i : Nat} (hi : i < 2) : (lo32 (qword qinvV i)).toNat = montQInv := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> decide

/-- `vredc` on a quadword `x`: `x + m · q`. -/
def redc (x qi qq : BitVec 64) : BitVec 64 := x + lo32 (lo32 x * lo32 qi) * lo32 qq

theorem redc_toNat {x qi qq : BitVec 64} (hqi : (lo32 qi).toNat = montQInv) (hqq : (lo32 qq).toNat = q)
    (hx : x.toNat < q * 2 ^ 32) : (redc x qi qq).toNat = mont x.toNat * 2 ^ 32 := by
  have hm : (lo32 (lo32 x * lo32 qi)).toNat = montM x.toNat := by
    rw [lo32_toNat, BitVec.toNat_mul, lo32_toNat, hqi, montM, Nat.mod_mod_of_dvd _ (by decide)]
  have hmq : (lo32 (lo32 x * lo32 qi) * lo32 qq).toNat = montM x.toNat * q := by
    rw [BitVec.toNat_mul, hm, hqq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (montM_lt _) (by decide))
      (by decide))
  rw [redc, BitVec.toNat_add, hmq, ← mont_mul]
  have := mont_lt hx
  rw [q_eq] at this
  exact Nat.mod_eq_of_lt (by omega_using [this])

theorem redc_hi {x qi qq : BitVec 64} (hqi : (lo32 qi).toNat = montQInv) (hqq : (lo32 qq).toNat = q)
    (hx : x.toNat < q * 2 ^ 32) : ((redc x qi qq).extractLsb' 32 32).toNat = mont x.toNat := by
  rw [BitVec.extractLsb'_toNat, redc_toNat hqi hqq hx, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (by decide)]
  have := mont_lt hx
  rw [q_eq] at this
  exact Nat.mod_eq_of_lt (by omega_using [this])

theorem redc_lo {x qi qq : BitVec 64} (hqi : (lo32 qi).toNat = montQInv) (hqq : (lo32 qq).toNat = q)
    (hx : x.toNat < q * 2 ^ 32) : (redc x qi qq).extractLsb' 0 32 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, redc_toNat hqi hqq hx, Nat.shiftRight_zero, Nat.mul_mod_left]
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
  rw [Nat.div_eq_of_lt (by omega_using [])]; rfl

/-! ## `vmont` -/

/-- The register `vmont d z zo` leaves in `d`. -/
def montV (d z zo : BitVec 128) : BitVec 128 :=
  let u := shufDwords d 0xF5
  let a := XBinOp.eval .pmuludq d z
  let b := XBinOp.eval .pmuludq u zo
  XBinOp.eval .por
    (XShiftOp.eval .psrlq (XBinOp.eval .paddq a (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq a qinvV) qV)) 32)
    (XBinOp.eval .paddq b (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq b qinvV) qV))

theorem qword_vredc (a : BitVec 128) {j : Nat} (hj : j < 2) :
    qword (XBinOp.eval .paddq a (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq a qinvV) qV)) j =
      redc (qword a j) (qword qinvV j) (qword qV j) := by
  rw [qword_paddq _ _ hj, qword_pmuludq _ _ hj, qword_pmuludq _ _ hj]; rfl

theorem toNat_qword_pmuludq (x y : BitVec 128) {j : Nat} (hj : j < 2) :
    (qword (XBinOp.eval .pmuludq x y) j).toNat = (dword x (2 * j)).toNat * (dword y (2 * j)).toNat := by
  rw [qword_pmuludq _ _ hj, toNat_lo32_mul, dword_lo, dword_lo, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero]

/-- Each doubleword of `montV d z zo` is `mont` of the product of those of
`d` and `z`. -/
theorem dword_montV {d z zo : BitVec 128} (hzo : ∀ j < 2, dword zo (2 * j) = dword z (2 * j + 1))
    (hb : ∀ i < 4, (dword d i).toNat * (dword z i).toNat < q * 2 ^ 32) {i : Nat} (hi : i < 4) :
    (dword (montV d z zo) i).toNat = mont ((dword d i).toNat * (dword z i).toNat) := by
  have hqi : ∀ j < 2, (lo32 (qword qinvV j)).toNat = montQInv := fun j hj => lo32_qword_qinvV hj
  have hqq : ∀ j < 2, (lo32 (qword qV j)).toNat = q := fun j hj => lo32_qword_qV hj
  rw [montV, dword_por]
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j < 2, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega_using [hi], by omega_using []⟩
  all_goals
    have hx : (qword (XBinOp.eval .pmuludq d z) j).toNat = (dword d (2 * j)).toNat * (dword z (2 * j)).toNat :=
      toNat_qword_pmuludq d z hj
    have hy : (qword (XBinOp.eval .pmuludq (shufDwords d 0xF5) zo) j).toNat =
        (dword d (2 * j + 1)).toNat * (dword z (2 * j + 1)).toNat := by
      rw [toNat_qword_pmuludq _ _ hj, hzo j hj, dword_shufDwords _ _ (by omega_using [hj])]
      rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  · -- an even doubleword: the quotient of the even product, moved down
    rw [dword_lo, dword_lo, qword_psrlq32 _ hj, qword_vredc _ hj, qword_vredc _ hj,
      redc_lo (hqi j hj) (hqq j hj) (by rw [hy]; exact hb _ (by omega_using [hj])), or_zero_toNat, lo_shr32,
      redc_hi (hqi j hj) (hqq j hj) (by rw [hx]; exact hb _ (by omega_using [hj])), hx]
  · -- an odd doubleword: the quotient of the odd product, in place
    rw [dword_hi, dword_hi, qword_psrlq32 _ hj, hi_shr32, zero_or_toNat, qword_vredc _ hj,
      redc_hi (hqi j hj) (hqq j hj) (by rw [hy]; exact hb _ (by omega_using [hj])), hy]

/-! ## Conditional additions and subtractions of `q` -/

/-- `q` as a doubleword. -/
def qB : BitVec 32 := 8380417#32

theorem dword_qV {i : Nat} (hi : i < 4) : dword qV i = qB := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

/-- `vcadd` on a doubleword: `d + q` if `d` is negative (as a signed doubleword). -/
def caddL (d : BitVec 32) : BitVec 32 := d + (d.sshiftRight (min (31 : BitVec 8).toNat 32) &&& qB)

/-- `vcsub` on a doubleword. -/
def csubL (d : BitVec 32) : BitVec 32 := caddL (d - qB)

theorem sshiftRight31 (d : BitVec 32) :
    d.sshiftRight (min (31 : BitVec 8).toNat 32) = if d.toNat < 2 ^ 31 then 0 else -1 := by
  rw [show min (31 : BitVec 8).toNat 32 = 31 from rfl]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, MlKem.X86_64.W.toInt32]
  have := d.isLt
  split
  · rw [show (0 : BitVec 32).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega_arith
  · rw [show (-1 : BitVec 32).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega_arith

theorem caddL_toNat (d : BitVec 32) :
    (caddL d).toNat = if d.toNat < 2 ^ 31 then d.toNat else (d.toNat + q) % 2 ^ 32 := by
  rw [caddL, sshiftRight31]
  split
  · rw [show (0 : BitVec 32) &&& qB = 0 by decide]; exact congrArg BitVec.toNat (BitVec.add_zero d)
  · rw [show (-1 : BitVec 32) &&& qB = qB by decide, BitVec.toNat_add]; rfl

/-- `vcsub` reduces a doubleword less than `2q`. -/
theorem csubL_toNat {d : BitVec 32} (h : d.toNat < 2 * q) : (csubL d).toNat = condSub d.toNat := by
  have e : (d - qB).toNat = (d.toNat + 2 ^ 32 - q) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]; rw [q_eq] at *; simp only [qB, BitVec.toNat_ofNat]; omega_using []
  rw [csubL, caddL_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega_arith

/-- The sum of two reduced doublewords, reduced by `vcsub`. -/
theorem addD_toNat {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (csubL (a + b)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add]; rw [q_eq] at *; omega_using [ha, hb]
  rw [csubL_toNat (by rw [e]; omega_using [ha, hb]), e]

/-- The difference of two reduced doublewords, reduced by `vcadd`. -/
theorem subD_toNat {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (caddL (a - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a - b).toNat = (a.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega_using []
  rw [caddL_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega_arith

/-- `b - a + q` of two reduced doublewords, which `vibfly` multiplies by the zeta. -/
theorem subq_toNat {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (b - a + qB).toNat = b.toNat + q - a.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_sub]; rw [q_eq] at *; simp only [qB, BitVec.toNat_ofNat]; omega_using [ha, hb]

/-! ## Butterflies, lane by lane -/

/-- A product by a zeta in Montgomery form, reduced: `ζ · y`. -/
theorem mulZ {b z m : BitVec 32} {y ζ : Spec.MlDsa.Zq} (hb : b.toNat = y.val) (hz : z.toNat = ζ.val * 2 ^ 32 % q)
    (hm : m.toNat = mont (b.toNat * z.toNat)) : (csubL m).toNat = (ζ * y).val := by
  have hx : b.toNat * z.toNat < q * 2 ^ 32 := by
    rw [hb, hz]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt y) (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
      (by decide)) (by decide)
  rw [csubL_toNat (by rw [hm]; exact mont_lt hx), hm, condSub_mont hx, hb, hz, mont_mulR, val_mul,
    Nat.mul_comm]

/-- The lanes of `vbfly`: `x + ζ · y` and `x - ζ · y`, from `t = ζ · y`. -/
theorem bflyD {a t : BitVec 32} {x y ζ : Spec.MlDsa.Zq} (ha : a.toNat = x.val) (ht : t.toNat = (ζ * y).val) :
    (csubL (a + t)).toNat = (x + ζ * y).val ∧ (caddL (a - t)).toNat = (x - ζ * y).val := by
  have hx := val_lt x
  have hzy := val_lt (ζ * y)
  rw [addD_toNat (by rw [ha]; exact hx) (by rw [ht]; exact hzy),
    subD_toNat (by rw [ha]; exact hx) (by rw [ht]; exact hzy), ha, ht, val_add, val_sub]
  exact ⟨rfl, rfl⟩

/-- The lanes of `vibfly`: `x + y` and `ζ · (y - x)`. -/
theorem ibflyD {a b z m : BitVec 32} {x y ζ : Spec.MlDsa.Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 2 ^ 32 % q) (hm : m.toNat = mont ((b - a + qB).toNat * z.toNat)) :
    (csubL (a + b)).toNat = (x + y).val ∧ (csubL m).toNat = (ζ * (y - x)).val := by
  have hx := val_lt x
  have hy := val_lt y
  have e := subq_toNat (a := a) (b := b) (by rw [ha]; exact hx) (by rw [hb]; exact hy)
  refine ⟨by rw [addD_toNat (by rw [ha]; exact hx) (by rw [hb]; exact hy), ha, hb, val_add], ?_⟩
  have hb' : (b - a + qB).toNat < q * 2 ^ 32 := by rw [e, ha, hb]; rw [q_eq] at *; omega_using []
  have hx' : (b - a + qB).toNat * z.toNat < q * 2 ^ 32 := by
    rw [hz]; rw [e, ha, hb] at hb' ⊢
    have := Nat.mod_lt (ζ.val * 2 ^ 32) (show 0 < q by decide)
    rw [q_eq] at *
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (show y.val + 8380417 - x.val < 2 * 8380417 by omega_using [hy])
      (Nat.le_of_lt this) (by decide)) (by decide)
  rw [csubL_toNat (by rw [hm]; exact mont_lt hx'), hm, condSub_mont hx', hz, mont_mulR, e, ha, hb,
    val_mul, val_sub', Nat.mul_mod_mod, Nat.mul_comm ζ.val,
    Nat.add_sub_assoc (Nat.le_of_lt x.isLt) y.val]

end VG.Proof.MlDsa.X86_64.Arith

end

end

/-!
# ML-DSA on x86-64: coefficients in the doublewords of SSE registers

A register holds four coefficients (`DLanes`), and the butterflies `vbfly` and
`vibfly` compute four butterflies of the specification at once (`vbfly_ok`,
`vibfly_ok`), from `q` and `-q⁻¹` in `xmm15` and `xmm14` (`VConsts`), with the
zetas in Montgomery form in `xmm13` (`ZLanes`) and its odd doublewords in the
even ones of `xmm12` (`ZOdd`).
-/

@[expose] public section

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
  q : s.xmm .xmm15 = qV
  qinv : s.xmm .xmm14 = qinvV

theorem VConsts.setXmm {s : State} (hc : VConsts s) {d : XReg} (h14 : XReg.xmm14 ≠ d)
    (h15 : XReg.xmm15 ≠ d) (v : BitVec 128) : VConsts (s.setXmm d v) :=
  ⟨by rw [xmm_setXmm, ifn h15]; exact hc.q, by rw [xmm_setXmm, ifn h14]; exact hc.qinv⟩

theorem xonly_vconsts {rs : List XReg} {s s' : State} (h : XOnly rs s s') (hc : VConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : VConsts s' :=
  ⟨by rw [h.xmm _ h15, hc.q], by rw [h.xmm _ h14, hc.qinv]⟩

/-! ## Registers -/

/-- `vcadd` on a register. -/
def caddV (d : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd d (XBinOp.eval .pand (XShiftOp.eval .psrad d 31) qV)

/-- `vcsub` on a register. -/
def csubV (d : BitVec 128) : BitVec 128 := caddV (XBinOp.eval .psubd d qV)

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

theorem dword_caddV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (caddV d) i = caddL (dword d i) := by
  rw [caddV, dword_paddd _ _ hi, dword_pand, dword_psrad _ _ hi, dword_qV hi]; rfl

theorem dword_csubV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (csubV d) i = csubL (dword d i) := by
  rw [csubV, dword_caddV _ hi, dword_psubd _ _ hi, dword_qV hi]; rfl

/-- A reduced coefficient times a zeta in Montgomery form is less than `q · 2³²`. -/
theorem prod_lt {y z : BitVec 128} {f ζ : Nat → Zq} (hy : DLanes y f) (hz : ZLanes z ζ) :
    ∀ i < 4, (dword y i).toNat * (dword z i).toNat < q * 2 ^ 32 := fun i hi => by
  rw [hy i hi, hz i hi]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt (f i)) (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
    (by decide)) (by decide)

theorem subq_mul_lt {a b c : Nat} (ha : a < 8380417) (hb : b < 8380417) (hc : c < q) :
    (b + q - a) * c < q * 2 ^ 32 := by
  rw [q_eq] at *
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (show b + 8380417 - a < 2 * 8380417 by omega)
    (Nat.le_of_lt hc) (by decide)) (by decide)

/-- By `(rfl)`, not `rfl`: `simp` uses a lemma proven by `rfl` as a definitional
rewrite, and the kernel then compares `XBinOp.eval .movdqa a b` with `b`
itself: where `b` is another `XBinOp.eval`, it unfolds both. -/
theorem eval_movdqa (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := (rfl)

/-! ## Butterflies -/

theorem vbfly_ok {s : State} (hc : VConsts s) {x y ζ : Nat → Zq} (hx : DLanes (s.xmm .xmm0) x)
    (hy : DLanes (s.xmm .xmm1) y) (hz : ZLanes (s.xmm .xmm13) ζ) (ho : ZOdd (s.xmm .xmm13) (s.xmm .xmm12)) :
    WP isa (.block vbfly) s fun s' => DLanes (s'.xmm .xmm0) (fun i => x i + ζ i * y i) ∧
      DLanes (s'.xmm .xmm3) (fun i => x i - ζ i * y i) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' := by
  simp only [vbfly, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (csubV (XBinOp.eval .paddd (s.xmm .xmm0)
      (csubV (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))))) _
    intro i hi
    rw [dword_csubV _ hi, dword_paddd _ _ hi, dword_csubV _ hi]
    exact (bflyD (hx i hi) (mulZ (hy i hi) (hz i hi) (dword_montV ho (prod_lt hy hz) hi))).1
  · change DLanes (caddV (XBinOp.eval .psubd (s.xmm .xmm0)
      (csubV (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))))) _
    intro i hi
    rw [dword_caddV _ hi, dword_psubd _ _ hi, dword_csubV _ hi]
    exact (bflyD (hx i hi) (mulZ (hy i hi) (hz i hi) (dword_montV ho (prod_lt hy hz) hi))).2

theorem vibfly_ok {s : State} (hc : VConsts s) {x y ζ : Nat → Zq} (hx : DLanes (s.xmm .xmm0) x)
    (hy : DLanes (s.xmm .xmm1) y) (hz : ZLanes (s.xmm .xmm13) ζ) (ho : ZOdd (s.xmm .xmm13) (s.xmm .xmm12)) :
    WP isa (.block vibfly) s fun s' => DLanes (s'.xmm .xmm0) (fun i => x i + y i) ∧
      DLanes (s'.xmm .xmm3) (fun i => ζ i * (y i - x i)) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' := by
  simp only [vibfly, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  have e : ∀ i < 4, dword (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) qV) i =
      dword (s.xmm .xmm1) i - dword (s.xmm .xmm0) i + qB := fun i hi => by
    rw [dword_paddd _ _ hi, dword_psubd _ _ hi, dword_qV hi]
  have hb : ∀ i < 4, (dword (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) qV) i).toNat *
      (dword (s.xmm .xmm13) i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [e i hi, subq_toNat (by rw [hx i hi]; exact val_lt _) (by rw [hy i hi]; exact val_lt _), hx i hi, hy i hi,
      hz i hi]
    exact subq_mul_lt (val_lt (x i)) (val_lt (y i)) (Nat.mod_lt _ (by decide))
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (csubV (XBinOp.eval .paddd (s.xmm .xmm0) (s.xmm .xmm1))) _
    intro i hi
    rw [dword_csubV _ hi, dword_paddd _ _ hi, addD_toNat (by rw [hx i hi]; exact val_lt _)
      (by rw [hy i hi]; exact val_lt _), hx i hi, hy i hi, val_add]
  · change DLanes (csubV (montV (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) qV)
      (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    rw [dword_csubV _ hi]
    exact (ibflyD (hx i hi) (hy i hi) (hz i hi) (by rw [dword_montV ho hb hi, e i hi])).2

end VG.Proof.MlDsa.X86_64.Arith
