import VerifiedGarbage.Impl.MlKem.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.MlKem.X86_64.Vec
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VArith`. -/
section

/-!
# ML-KEM on x86-64: arithmetic modulo `q` in 16-bit words

What `vmont`, `vcadd` and `vcsub` (`Impl/MlKem/X86_64/Vec.lean`) compute in
each word (`montW`, `caddW`, `csubW`), on the words' signed values
(`BitVec.toInt`):

* `montW_spec`: `montW d z` is in `(-q, q)` and congruent to
  `d · z · 2⁻¹⁶` modulo `q`, if `|d · z| < q · 2¹⁵`;
* `caddW_spec`, `csubW_spec`: the value modulo `q`, in `[0, q)`, of a word in
  `(-q, q)` or `[0, 2q)`.
-/

namespace VG.Proof.MlKem.X86_64.W

open VG VG.X86_64 VG.Proof.MlKem

/-- `q` as a word. -/
def qW : BitVec 16 := 3329

/-- `q⁻¹ mod 2¹⁶` as a word. -/
def qinvW : BitVec 16 := 62209

/-- The word `vmont` leaves of the words `d` and `z`. -/
def montW (d z : BitVec 16) : BitVec 16 :=
  (mulWordsSigned d z).extractLsb' 16 16 -
    (mulWordsSigned ((mulWordsSigned ((mulWordsSigned d z).extractLsb' 0 16) VG.Proof.MlKem.X86_64.W.qinvW).extractLsb' 0 16)
      VG.Proof.MlKem.X86_64.W.qW).extractLsb' 16 16

/-- The word `vcadd` leaves of `d`. -/
def caddW (d : BitVec 16) : BitVec 16 := d + ((d.sshiftRight (min 15 16)) &&& VG.Proof.MlKem.X86_64.W.qW)

/-- The word `vcsub` leaves of `d`. -/
def csubW (d : BitVec 16) : BitVec 16 := VG.Proof.MlKem.X86_64.W.caddW (d - VG.Proof.MlKem.X86_64.W.qW)

/-! ## Words as integers -/

theorem toInt16 (x : BitVec 16) :
    x.toInt = if x.toNat < 32768 then (x.toNat : Int) else (x.toNat : Int) - 65536 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega

theorem toInt32 (x : BitVec 32) :
    x.toInt = if x.toNat < 2147483648 then (x.toNat : Int) else (x.toNat : Int) - 4294967296 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega

theorem toInt16_bounds (x : BitVec 16) : -32768 ≤ x.toInt ∧ x.toInt < 32768 := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16]; have := x.isLt; split <;> omega

/-- A word is determined by its value modulo `2¹⁶` and its range. -/
theorem toInt16_eq {x : BitVec 16} {v : Int} (h1 : -32768 ≤ v) (h2 : v < 32768)
    (h : ((x.toNat : Int) - v) % 65536 = 0) : x.toInt = v := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16]; have := x.isLt; split <;> omega

theorem toNat16_eq {x : BitVec 16} : (x.toNat : Int) % 65536 = x.toInt % 65536 := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16]; have := x.isLt; split <;> omega

/-- The product of two words is at most `2³⁰` in magnitude. -/
theorem mul_bounds (a b : BitVec 16) : -(2 ^ 30 : Int) ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 2 ^ 30 := by
  have ha := VG.Proof.MlKem.X86_64.W.toInt16_bounds a
  have hb := VG.Proof.MlKem.X86_64.W.toInt16_bounds b
  have hn : (a.toInt * b.toInt).natAbs ≤ 32768 * 32768 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 := Int.le_natAbs (a := a.toInt * b.toInt)
  have h2 := Int.le_natAbs (a := -(a.toInt * b.toInt))
  rw [Int.natAbs_neg] at h2
  omega

theorem toInt_mulWordsSigned (a b : BitVec 16) : (mulWordsSigned a b).toInt = a.toInt * b.toInt := by
  rw [mulWordsSigned, BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by decide),
    BitVec.toInt_signExtend_of_le (by decide)]
  have := VG.Proof.MlKem.X86_64.W.mul_bounds a b
  apply Int.bmod_eq_of_le
  · rw [show (((2 ^ 32 : Nat) : Int) / 2) = 2147483648 from rfl]; omega
  · rw [show ((((2 ^ 32 : Nat) : Int) + 1) / 2) = 2147483648 from rfl]; omega

/-- The high word of a doubleword: its value divided by `2¹⁶`, rounded down. -/
theorem toInt_hi (x : BitVec 32) : (x.extractLsb' 16 16).toInt = x.toInt / 65536 := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16, VG.Proof.MlKem.X86_64.W.toInt32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  simp only [Nat.reducePow]
  split <;> split <;> omega

/-- The low word of a doubleword: its value modulo `2¹⁶`. -/
theorem toInt_lo (x : BitVec 32) : ((x.extractLsb' 0 16).toInt - x.toInt) % 65536 = 0 := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16, VG.Proof.MlKem.X86_64.W.toInt32, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have := x.isLt
  simp only [Nat.reducePow]
  split <;> split <;> omega

theorem toInt_sub16 {a b : BitVec 16} (h1 : -32768 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 32768) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]; exact Int.bmod_eq_of_le (by simpa using h1) (by simpa using h2)

theorem toInt_add16 {a b : BitVec 16} (h1 : -32768 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 32768) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]; exact Int.bmod_eq_of_le (by simpa using h1) (by simpa using h2)

theorem qW_toInt : qW.toInt = 3329 := by decide
theorem qinvW_toInt : qinvW.toInt = -3327 := by decide

/-! ## Montgomery reduction -/

/-- `montW d z` is in `(-q, q)` and `2¹⁶ · montW d z ≡ d · z (mod q)`. -/
theorem montW_spec {d z : BitVec 16} (h1 : -(3329 * 32768) < d.toInt * z.toInt)
    (h2 : d.toInt * z.toInt < 3329 * 32768) :
    -3329 < (VG.Proof.MlKem.X86_64.W.montW d z).toInt ∧ (VG.Proof.MlKem.X86_64.W.montW d z).toInt < 3329 ∧
      ((VG.Proof.MlKem.X86_64.W.montW d z).toInt * 65536 - d.toInt * z.toInt) % 3329 = 0 := by
  generalize hP : d.toInt * z.toInt = P at h1 h2
  have eP : (mulWordsSigned d z).toInt = P := by rw [VG.Proof.MlKem.X86_64.W.toInt_mulWordsSigned, hP]
  generalize hL : (mulWordsSigned d z).extractLsb' 0 16 = L
  have hL' := VG.Proof.MlKem.X86_64.W.toInt_lo (mulWordsSigned d z)
  rw [hL, eP] at hL'
  have bL := VG.Proof.MlKem.X86_64.W.toInt16_bounds L
  generalize hT : (mulWordsSigned L VG.Proof.MlKem.X86_64.W.qinvW).extractLsb' 0 16 = T
  have hT' := VG.Proof.MlKem.X86_64.W.toInt_lo (mulWordsSigned L VG.Proof.MlKem.X86_64.W.qinvW)
  rw [hT, VG.Proof.MlKem.X86_64.W.toInt_mulWordsSigned, VG.Proof.MlKem.X86_64.W.qinvW_toInt] at hT'
  have bT := VG.Proof.MlKem.X86_64.W.toInt16_bounds T
  have hH := VG.Proof.MlKem.X86_64.W.toInt_hi (mulWordsSigned d z)
  rw [eP] at hH
  have hM := VG.Proof.MlKem.X86_64.W.toInt_hi (mulWordsSigned T VG.Proof.MlKem.X86_64.W.qW)
  rw [VG.Proof.MlKem.X86_64.W.toInt_mulWordsSigned, VG.Proof.MlKem.X86_64.W.qW_toInt] at hM
  have e : VG.Proof.MlKem.X86_64.W.montW d z = (mulWordsSigned d z).extractLsb' 16 16 - (mulWordsSigned T VG.Proof.MlKem.X86_64.W.qW).extractLsb' 16 16 := by
    rw [VG.Proof.MlKem.X86_64.W.montW, hL, hT]
  have hc : (P - T.toInt * 3329) % 65536 = 0 := by omega
  have hd : P / 65536 - T.toInt * 3329 / 65536 = (P - T.toInt * 3329) / 65536 := by omega
  rw [e, VG.Proof.MlKem.X86_64.W.toInt_sub16 (by omega) (by omega), hH, hM, hd]
  omega

/-! ## Conditional additions of `q` -/

theorem sshiftRight15 (d : BitVec 16) :
    d.sshiftRight (min 15 16) = if d.toInt < 0 then -1 else 0 := by
  rw [show min 15 16 = 15 from rfl]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight]
  have := VG.Proof.MlKem.X86_64.W.toInt16_bounds d
  split
  · rw [show (-1 : BitVec 16).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega
  · rw [show (0 : BitVec 16).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega

/-- `caddW d` is the value of `d ∈ [-q, q)` modulo `q`. -/
theorem caddW_spec {d : BitVec 16} (h1 : -3329 ≤ d.toInt) (h2 : d.toInt < 3329) :
    (VG.Proof.MlKem.X86_64.W.caddW d).toInt = d.toInt % 3329 := by
  rw [VG.Proof.MlKem.X86_64.W.caddW, VG.Proof.MlKem.X86_64.W.sshiftRight15]
  split
  · rw [show (-1 : BitVec 16) &&& VG.Proof.MlKem.X86_64.W.qW = VG.Proof.MlKem.X86_64.W.qW by decide, VG.Proof.MlKem.X86_64.W.toInt_add16 (by rw [VG.Proof.MlKem.X86_64.W.qW_toInt]; omega)
      (by rw [VG.Proof.MlKem.X86_64.W.qW_toInt]; omega), VG.Proof.MlKem.X86_64.W.qW_toInt]
    omega
  · rw [show d + ((0 : BitVec 16) &&& VG.Proof.MlKem.X86_64.W.qW) = d by rw [show (0 : BitVec 16) &&& VG.Proof.MlKem.X86_64.W.qW = 0 by decide]; simp]
    omega

/-- `csubW d` is the value of `d ∈ [0, 2q)` modulo `q`. -/
theorem csubW_spec {d : BitVec 16} (h1 : 0 ≤ d.toInt) (h2 : d.toInt < 2 * 3329) :
    (VG.Proof.MlKem.X86_64.W.csubW d).toInt = d.toInt % 3329 := by
  have e := VG.Proof.MlKem.X86_64.W.toInt_sub16 (a := d) (b := VG.Proof.MlKem.X86_64.W.qW) (by rw [VG.Proof.MlKem.X86_64.W.qW_toInt]; omega) (by rw [VG.Proof.MlKem.X86_64.W.qW_toInt]; omega)
  rw [VG.Proof.MlKem.X86_64.W.qW_toInt] at e
  rw [VG.Proof.MlKem.X86_64.W.csubW, VG.Proof.MlKem.X86_64.W.caddW_spec (d := d - VG.Proof.MlKem.X86_64.W.qW) (by rw [e]; omega) (by rw [e]; omega), e]
  omega

/-! ## Coefficients -/

open VG.Spec.MlKem (Zq)

theorem toInt_of_lt {a : BitVec 16} (h : a.toNat < 3329) : a.toInt = a.toNat := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16, ite_eq_left_of_eq_true _ _ (by simp; omega)]

theorem toNat_of_toInt {a : BitVec 16} (h : 0 ≤ a.toInt) : (a.toNat : Int) = a.toInt := by
  rw [VG.Proof.MlKem.X86_64.W.toInt16] at h ⊢; have := a.isLt; split at h <;> [rw [ite_eq_left_of_eq_true _ _ (by simp; omega)]; omega]

/-- Cancelling `2¹⁶` modulo `q`: `2¹⁶ · 169 ≡ 1 (mod q)`. -/
theorem cancel_R {r P Y : Int} (h1 : (r * 65536 - P) % 3329 = 0) (h2 : (P - Y * 65536) % 3329 = 0) :
    r % 3329 = Y % 3329 := by
  omega

/-- `b · (ζ · 2¹⁶ mod q) ≡ y · ζ · 2¹⁶ (mod q)` for `b ≡ y (mod q)`. -/
theorem mul_zm {b y ζ z : Int} (hby : (b - y) % 3329 = 0) (hz : z = ζ * 65536 % 3329) :
    (b * z - y * ζ * 65536) % 3329 = 0 := by
  have e : b * z - y * ζ * 65536 = (b - y) * z + y * (z - ζ * 65536) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_assoc y ζ]; omega
  rw [e]
  apply Int.emod_eq_zero_of_dvd
  refine Int.dvd_add (Int.dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hby))
    (Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero ?_))
  rw [hz]; omega

/-- `ζ · y mod q`, from a word `b ≡ y (mod q)` in `(-q, q)` and the word
`ζ · 2¹⁶ mod q`. -/
theorem mulZ_spec {b z : BitVec 16} {y ζ : Zq} (hb1 : -3329 < b.toInt) (hb2 : b.toInt < 3329)
    (hby : (b.toInt - (y.val : Int)) % 3329 = 0) (hz : z.toNat = ζ.val * 65536 % 3329) :
    (VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW b z)).toInt = (ζ * y).val := by
  have hzl : z.toNat < 3329 := by rw [hz]; exact Nat.mod_lt _ (by decide)
  have hzi := VG.Proof.MlKem.X86_64.W.toInt_of_lt hzl
  have hn : (b.toInt * z.toInt).natAbs ≤ 3328 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 := Int.le_natAbs (a := b.toInt * z.toInt)
  have h2 := Int.le_natAbs (a := -(b.toInt * z.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := VG.Proof.MlKem.X86_64.W.montW_spec (d := b) (z := z) (by omega) (by omega)
  have hzI : z.toInt = (ζ.val : Int) * 65536 % 3329 := by rw [hzi]; omega
  have hm := VG.Proof.MlKem.X86_64.W.mul_zm (ζ := (ζ.val : Int)) hby hzI
  rw [VG.Proof.MlKem.X86_64.W.caddW_spec (Int.le_of_lt m1) m2, val_mul, VG.Proof.MlKem.X86_64.W.cancel_R m3 hm, Int.natCast_emod, Int.natCast_mul,
    Int.mul_comm (ζ.val : Int)]
  rfl

/-- The value modulo `q` of a sum or a difference of two words less than `q`. -/
theorem addsub_int {A T : Int} (hA : 0 ≤ A ∧ A < 3329) (hT : 0 ≤ T ∧ T < 3329) :
    (-32768 ≤ A + T ∧ A + T < 32768 ∧ 0 ≤ A + T ∧ A + T < 2 * 3329) ∧
      (-32768 ≤ A - T ∧ A - T < 32768 ∧ -3329 ≤ A - T ∧ A - T < 3329) := by
  omega

/-- The two words of a butterfly of Algorithm 9 (`vbfly`): `x + ζ y` and
`x - ζ y`, from the words `x`, `y` and `ζ · 2¹⁶ mod q`. -/
theorem bflyW {a b z : BitVec 16} {x y ζ : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 65536 % 3329) :
    (VG.Proof.MlKem.X86_64.W.csubW (a + VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW b z))).toNat = (x + ζ * y).val ∧
      (VG.Proof.MlKem.X86_64.W.caddW (a - VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW b z))).toNat = (x - ζ * y).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := VG.Proof.MlKem.X86_64.W.toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := VG.Proof.MlKem.X86_64.W.toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  have ht := VG.Proof.MlKem.X86_64.W.mulZ_spec (b := b) (y := y) (ζ := ζ) (by rw [bi]; omega) (by rw [bi]; omega)
    (by rw [bi, Int.sub_self]; rfl) hz
  have hzy := val_lt (ζ * y)
  generalize VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW b z) = t at ht
  obtain ⟨⟨p1, p2, p3, p4⟩, ⟨m1, m2, m3, m4⟩⟩ :=
    VG.Proof.MlKem.X86_64.W.addsub_int (A := a.toInt) (T := t.toInt) (by rw [ai]; omega)
      (by rw [ht]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hzy⟩)
  rw [← VG.Proof.MlKem.X86_64.W.toInt_add16 p1 p2] at p3 p4
  rw [← VG.Proof.MlKem.X86_64.W.toInt_sub16 m1 m2] at m3 m4
  have c1 := VG.Proof.MlKem.X86_64.W.csubW_spec p3 p4
  have c2 := VG.Proof.MlKem.X86_64.W.caddW_spec m3 m4
  rw [VG.Proof.MlKem.X86_64.W.toInt_add16 p1 p2] at c1
  rw [VG.Proof.MlKem.X86_64.W.toInt_sub16 m1 m2] at c2
  have n1 := VG.Proof.MlKem.X86_64.W.toNat_of_toInt (a := VG.Proof.MlKem.X86_64.W.csubW (a + t)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  have n2 := VG.Proof.MlKem.X86_64.W.toNat_of_toInt (a := VG.Proof.MlKem.X86_64.W.caddW (a - t)) (by rw [c2]; exact Int.emod_nonneg _ (by decide))
  have v1 : (x + ζ * y).val = (x.val + (ζ * y).val) % 3329 := val_add' _ _
  have v2 : (x - ζ * y).val = (x.val + (3329 - (ζ * y).val)) % 3329 := val_sub' _ _
  rw [v1, v2]
  rw [c1, ai, ht] at n1
  rw [c2, ai, ht] at n2
  generalize (ζ * y).val = Z at *
  generalize x.val = X at *
  constructor <;> omega_using [n1, n2, hx, hzy]

/-- The two words of a butterfly of Algorithm 10 (`vibfly`): `x + y` and
`ζ (y - x)`. -/
theorem ibflyW {a b z : BitVec 16} {x y ζ : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 65536 % 3329) :
    (VG.Proof.MlKem.X86_64.W.csubW (a + b)).toNat = (x + y).val ∧ (VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW (b - a) z)).toNat = (ζ * (y - x)).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := VG.Proof.MlKem.X86_64.W.toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := VG.Proof.MlKem.X86_64.W.toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  have p1 : -32768 ≤ a.toInt + b.toInt := by rw [ai, bi]; omega
  have p2 : a.toInt + b.toInt < 32768 := by rw [ai, bi]; omega
  have m1 : -32768 ≤ b.toInt - a.toInt := by rw [ai, bi]; omega
  have m2 : b.toInt - a.toInt < 32768 := by rw [ai, bi]; omega
  have c1 := VG.Proof.MlKem.X86_64.W.csubW_spec (d := a + b) (by rw [VG.Proof.MlKem.X86_64.W.toInt_add16 p1 p2, ai, bi]; omega)
    (by rw [VG.Proof.MlKem.X86_64.W.toInt_add16 p1 p2, ai, bi]; omega)
  rw [VG.Proof.MlKem.X86_64.W.toInt_add16 p1 p2, ai, bi] at c1
  have n1 := VG.Proof.MlKem.X86_64.W.toNat_of_toInt (a := VG.Proof.MlKem.X86_64.W.csubW (a + b)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  rw [c1] at n1
  have hm := VG.Proof.MlKem.X86_64.W.mulZ_spec (b := b - a) (y := y - x) (ζ := ζ) (by rw [VG.Proof.MlKem.X86_64.W.toInt_sub16 m1 m2, ai, bi]; omega)
    (by rw [VG.Proof.MlKem.X86_64.W.toInt_sub16 m1 m2, ai, bi]; omega)
    (by
      have v : (y - x).val = (y.val + (3329 - x.val)) % 3329 := val_sub' _ _
      rw [VG.Proof.MlKem.X86_64.W.toInt_sub16 m1 m2, ai, bi, v]; omega) hz
  have hzy := val_lt (ζ * (y - x))
  have n2 := VG.Proof.MlKem.X86_64.W.toNat_of_toInt (a := VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW (b - a) z)) (by rw [hm]; exact Int.natCast_nonneg _)
  rw [hm] at n2
  have v1 : (x + y).val = (x.val + y.val) % 3329 := val_add' _ _
  rw [v1]
  generalize (ζ * (y - x)).val = Z at *
  generalize x.val = X at *
  generalize y.val = Y at *
  constructor <;> omega_using [n1, n2, hx, hy]

end VG.Proof.MlKem.X86_64.W

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VLanes`. -/
section

/-!
# ML-KEM on x86-64: coefficients in the words of SSE registers

A register holds eight coefficients (`Lanes`), and the butterflies `vbfly` and
`vibfly` compute eight butterflies of the specification at once (`vbfly_ok`,
`vibfly_ok`), from `q` and `q⁻¹` in `xmm15` and `xmm14` (`VConsts`), which
`vconsts` leaves there (`vconsts_ok`).

Blocks of SSE instructions only are run with `vrun`, which keeps the state a
chain of `setXmm`, whose registers the words' lemmas (`word_paddw`, …) read
lane by lane.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open W (qW qinvW)

/-- The words of `x` are the values of the coefficients `f 0, …, f 7`. -/
def Lanes (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ i < 8, (word x i).toNat = (f i).val

/-- The words of `x` are the zetas `ζ i · 2¹⁶ mod q` (Montgomery form). -/
def ZLanes (x : BitVec 128) (ζ : Nat → Zq) : Prop :=
  ∀ i < 8, (word x i).toNat = (ζ i).val * 65536 % 3329

/-- `q` in every word. -/
def qV : BitVec 128 := 0x0D010D010D010D010D010D010D010D01#128

/-- `q⁻¹ mod 2¹⁶` in every word. -/
def qinvV : BitVec 128 := 0xF301F301F301F301F301F301F301F301#128

theorem word_qV {i : Nat} (hi : i < 8) : word VG.Proof.MlKem.X86_64.qV i = VG.Proof.MlKem.X86_64.W.qW := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem word_qinvV {i : Nat} (hi : i < 8) : word VG.Proof.MlKem.X86_64.qinvV i = VG.Proof.MlKem.X86_64.W.qinvW := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The constants of the vector code are in place. -/
structure VConsts (s : State) : Prop where
  q : s.xmm .xmm15 = VG.Proof.MlKem.X86_64.qV
  qinv : s.xmm .xmm14 = VG.Proof.MlKem.X86_64.qinvV

/-- Everything but the SSE registers is as it was. -/
structure XKeep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem XKeep.refl (s : State) : VG.Proof.MlKem.X86_64.XKeep s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem XKeep.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.X86_64.XKeep s₁ s₂) (h₂ : VG.Proof.MlKem.X86_64.XKeep s₂ s₃) : VG.Proof.MlKem.X86_64.XKeep s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.mxcsr.trans h₁.mxcsr⟩

theorem xmm_setXmm (s : State) (d : XReg) (v : BitVec 128) (r : XReg) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl
theorem mxcsr_setXmm (s : State) (d : XReg) (v : BitVec 128) : (s.setXmm d v).mxcsr = s.mxcsr := rfl

/-- Runs a block of SSE instructions. -/
syntax "vrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vrun) => `(tactic| vrun [])
  | `(tactic| vrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
        Option.some.injEq, exists_eq_left', RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
        RegUpd.wr_setXmm, mxcsr_setXmm, xmm_setXmm, ite_true, ite_false, reduceCtorEq, $ls,*]))

/-! ## Montgomery products and conditional additions, word by word -/

/-- The words of `x` are `f 0, …, f 7`. -/
def WLanes (x : BitVec 128) (f : Nat → BitVec 16) : Prop := ∀ i < 8, word x i = f i

/-- Only the SSE registers `rs` changed. -/
structure XOnly (rs : List XReg) (s s' : State) : Prop extends VG.Proof.MlKem.X86_64.XKeep s s' where
  xmm : ∀ r ∉ rs, s'.xmm r = s.xmm r

theorem XOnly.trans {rs rs' : List XReg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.X86_64.XOnly rs s₁ s₂) (h₂ : VG.Proof.MlKem.X86_64.XOnly rs' s₂ s₃) :
    VG.Proof.MlKem.X86_64.XOnly (rs ++ rs') s₁ s₃ :=
  { toXKeep := h₁.toXKeep.trans h₂.toXKeep
    xmm := fun r hr => by
      rw [List.mem_append, not_or] at hr
      rw [h₂.xmm r hr.2, h₁.xmm r hr.1] }

theorem XOnly.mono {rs rs' : List XReg} {s s' : State} (h : VG.Proof.MlKem.X86_64.XOnly rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.MlKem.X86_64.XOnly rs' s s' := { toXKeep := h.toXKeep, xmm := fun r hr => h.xmm r fun h' => hr (hs r h') }

theorem XOnly.refl (rs : List XReg) (s : State) : VG.Proof.MlKem.X86_64.XOnly rs s s :=
  { toXKeep := XKeep.refl s, xmm := fun _ _ => rfl }

theorem XOnly.setXmm {rs : List XReg} {s s' : State} {d : XReg} (hd : d ∈ rs) (h : VG.Proof.MlKem.X86_64.XOnly rs s s')
    (v : BitVec 128) : VG.Proof.MlKem.X86_64.XOnly rs s (s'.setXmm d v) :=
  { gpr := h.gpr, mem := h.mem, rd := h.rd, wr := h.wr, mxcsr := h.mxcsr
    xmm := fun r hr => by
      rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifn (fun (e : r = d) => hr (e ▸ hd))]; exact h.xmm r hr }

/-- `XOnly` of a chain of `setXmm` of the registers `rs`. -/
syntax "xonly" : tactic
macro_rules
  | `(tactic| xonly) => `(tactic| (repeat (refine XOnly.setXmm (by simp) ?_ _)) <;> exact XOnly.refl _ _)

theorem VConsts.setXmm {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) {d : XReg} (h14 : XReg.xmm14 ≠ d)
    (h15 : XReg.xmm15 ≠ d) (v : BitVec 128) : VG.Proof.MlKem.X86_64.VConsts (s.setXmm d v) :=
  ⟨by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifn h15]; exact hc.q, by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifn h14]; exact hc.qinv⟩

theorem XOnly.consts {rs : List XReg} {s s' : State} (h : VG.Proof.MlKem.X86_64.XOnly rs s s') (hc : VG.Proof.MlKem.X86_64.VConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : VG.Proof.MlKem.X86_64.VConsts s' :=
  ⟨by rw [h.xmm _ h15, hc.q], by rw [h.xmm _ h14, hc.qinv]⟩

theorem vmont_ok {d z t : XReg} (h2 : t ≠ d) (h3 : z ≠ t) (h5 : XReg.xmm15 ≠ d) (h6 : XReg.xmm14 ≠ t)
    (h7 : XReg.xmm15 ≠ t) {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) :
    WP isa (.block (vmont d z t)) s fun s' =>
      VG.Proof.MlKem.X86_64.WLanes (s'.xmm d) (fun i => W.montW (word (s.xmm d) i) (word (s.xmm z) i)) ∧ VG.Proof.MlKem.X86_64.XOnly [d, t] s s' := by
  simp only [vmont, xmov, xb]
  vrun [h2, h3, h5, h6, h7, h2.symm, h3.symm, h5.symm, h6.symm, h7.symm]
  refine ⟨fun i hi => ?_, ?_⟩
  swap
  · xonly
  rw [hc.q, hc.qinv]
  simp only [word_psubw _ _ hi, word_pmulhw _ _ hi, word_pmullw _ _ hi, word_movdqa, VG.Proof.MlKem.X86_64.word_qV hi,
    VG.Proof.MlKem.X86_64.word_qinvV hi]
  rfl

theorem vcadd_ok {d t : XReg} (h1 : t ≠ d) (h5 : XReg.xmm15 ≠ t) {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) :
    WP isa (.block (vcadd d t)) s fun s' =>
      VG.Proof.MlKem.X86_64.WLanes (s'.xmm d) (fun i => W.caddW (word (s.xmm d) i)) ∧ VG.Proof.MlKem.X86_64.XOnly [d, t] s s' := by
  simp only [vcadd, xmov, xb]
  vrun [h1, h5, h1.symm, h5.symm]
  refine ⟨fun i hi => ?_, ?_⟩
  swap
  · xonly
  rw [hc.q]
  simp only [word_paddw _ _ hi, word_pand _ _, word_psraw _ _ hi, word_movdqa, VG.Proof.MlKem.X86_64.word_qV hi]
  rfl

theorem vcsub_ok {d t : XReg} (h1 : t ≠ d) (h4 : XReg.xmm15 ≠ d) (h5 : XReg.xmm15 ≠ t)
    (h6 : XReg.xmm14 ≠ d) {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) :
    WP isa (.block (vcsub d t)) s fun s' =>
      VG.Proof.MlKem.X86_64.WLanes (s'.xmm d) (fun i => W.csubW (word (s.xmm d) i)) ∧ VG.Proof.MlKem.X86_64.XOnly [d, t] s s' := by
  rw [vcsub, show (xb .psubw d .xmm15 :: vcadd d t) = [xb .psubw d .xmm15] ++ vcadd d t from rfl,
    WP.block_append_iff]
  simp only [xb]
  vrun [h4, h4.symm]
  refine WP.mono (VG.Proof.MlKem.X86_64.vcadd_ok h1 h5 ⟨by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifn h4]; exact hc.q,
    by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifn h6]; exact hc.qinv⟩) fun s' ⟨hl, ho⟩ => ⟨fun i hi => ?_, ?_⟩
  · rw [hl i hi, VG.Proof.MlKem.X86_64.xmm_setXmm, ifp rfl]; dsimp only; rw [word_psubw _ _ hi, hc.q, VG.Proof.MlKem.X86_64.word_qV hi]; rfl
  · exact (XOnly.setXmm (by simp) (XOnly.refl [d] s) _ |>.trans ho).mono (by simp)

/-! ## Butterflies -/

theorem vbfly_ok {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) {x y ζ : Nat → Zq} (hx : VG.Proof.MlKem.X86_64.Lanes (s.xmm .xmm0) x)
    (hy : VG.Proof.MlKem.X86_64.Lanes (s.xmm .xmm1) y) (hz : VG.Proof.MlKem.X86_64.ZLanes (s.xmm .xmm13) ζ) :
    WP isa (.block vbfly) s fun s' => VG.Proof.MlKem.X86_64.Lanes (s'.xmm .xmm0) (fun i => x i + ζ i * y i) ∧
      VG.Proof.MlKem.X86_64.Lanes (s'.xmm .xmm3) (fun i => x i - ζ i * y i) ∧ VG.Proof.MlKem.X86_64.XOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s' := by
  rw [vbfly, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vmont_ok (d := .xmm1) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vcadd_ok (d := .xmm1) (t := .xmm2) (by decide) (by decide)
    (o1.consts hc (by decide) (by decide))) fun s2 ⟨l2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [show (xmov .xmm3 .xmm0 :: xb .paddw .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) ++
      (xb .psubw .xmm3 .xmm1 :: vcadd .xmm3 .xmm2) =
      [xmov .xmm3 .xmm0, xb .paddw .xmm0 .xmm1] ++ (vcsub .xmm0 .xmm2 ++
        ([xb .psubw .xmm3 .xmm1] ++ vcadd .xmm3 .xmm2)) from rfl, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  have c2 := o12.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vcsub_ok (d := .xmm0) (t := .xmm2) (by decide) (by decide) (by decide) (by decide)
    ((c2.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm0) (by decide) (by decide) _))
    fun s3 ⟨l3, o3⟩ => ?_
  rw [WP.block_append_iff]
  vrun
  have c3 := o3.consts ((c2.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm0) (by decide)
    (by decide) _) (by decide) (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.vcadd_ok (d := .xmm3) (t := .xmm2) (by decide) (by decide)
    (c3.setXmm (d := .xmm3) (by decide) (by decide) _)) fun s4 ⟨l4, o4⟩ => ?_
  -- the words of the registers along the way
  have w0 : s2.xmm .xmm0 = s.xmm .xmm0 := o12.xmm _ (by decide)
  have w13 : s1.xmm .xmm13 = s.xmm .xmm13 := o1.xmm _ (by decide)
  have w31 : s3.xmm .xmm1 = s2.xmm .xmm1 := by rw [o3.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; rfl
  have w33 : s3.xmm .xmm3 = s2.xmm .xmm0 := by rw [o3.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; rfl
  have w40 : s4.xmm .xmm0 = s3.xmm .xmm0 := by rw [o4.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm]; rfl
  have t : ∀ i < 8, word (s2.xmm .xmm1) i = W.caddW (W.montW (word (s.xmm .xmm1) i) (word (s.xmm .xmm13) i)) :=
    fun i hi => by rw [l2 i hi]; dsimp only; rw [l1 i hi]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [w40, l3 i hi, VG.Proof.MlKem.X86_64.xmm_setXmm]; dsimp only
    rw [ifp rfl, word_paddw _ _ hi, t i hi, w0]
    exact (W.bflyW (hx i hi) (hy i hi) (hz i hi)).1
  · rw [l4 i hi, VG.Proof.MlKem.X86_64.xmm_setXmm, ifp rfl]; dsimp only
    rw [word_psubw _ _ hi, w31, w33, t i hi, w0]
    exact (W.bflyW (hx i hi) (hy i hi) (hz i hi)).2
  · refine ((o12.trans ((XOnly.setXmm (by simp) (XOnly.setXmm (by simp) (XOnly.refl [.xmm3, .xmm0] s2) _) _).trans
      (o3.trans ((XOnly.setXmm (by simp) (XOnly.refl [.xmm3] s3) _).trans o4)))).mono ?_)
    simp

theorem vibfly_ok {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) {x y ζ : Nat → Zq} (hx : VG.Proof.MlKem.X86_64.Lanes (s.xmm .xmm0) x)
    (hy : VG.Proof.MlKem.X86_64.Lanes (s.xmm .xmm1) y) (hz : VG.Proof.MlKem.X86_64.ZLanes (s.xmm .xmm13) ζ) :
    WP isa (.block vibfly) s fun s' => VG.Proof.MlKem.X86_64.Lanes (s'.xmm .xmm0) (fun i => x i + y i) ∧
      VG.Proof.MlKem.X86_64.Lanes (s'.xmm .xmm3) (fun i => ζ i * (y i - x i)) ∧ VG.Proof.MlKem.X86_64.XOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s' := by
  rw [vibfly, show (xmov .xmm3 .xmm1 :: xb .psubw .xmm3 .xmm0 :: xb .paddw .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) =
      [xmov .xmm3 .xmm1, xb .psubw .xmm3 .xmm0, xb .paddw .xmm0 .xmm1] ++ vcsub .xmm0 .xmm2 from rfl,
    List.append_assoc, List.append_assoc, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vcsub_ok (d := .xmm0) (t := .xmm2) (by decide) (by decide) (by decide) (by decide)
    (((hc.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm3) (by decide) (by decide)
      _).setXmm (d := .xmm0) (by decide) (by decide) _)) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts (((hc.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm3) (by decide)
    (by decide) _).setXmm (d := .xmm0) (by decide) (by decide) _) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vmont_ok (d := .xmm3) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) c1) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.vcadd_ok (d := .xmm3) (t := .xmm2) (by decide) (by decide)
    (o2.consts c1 (by decide) (by decide))) fun s3 ⟨l3, o3⟩ => ?_
  have w0 : s3.xmm .xmm0 = s1.xmm .xmm0 := (o2.trans o3).xmm _ (by decide)
  have w3 : s1.xmm .xmm3 = XBinOp.eval .psubw (s.xmm .xmm1) (s.xmm .xmm0) := by
    rw [o1.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; rfl
  have w13 : s1.xmm .xmm13 = s.xmm .xmm13 := by rw [o1.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [w0, l1 i hi, VG.Proof.MlKem.X86_64.xmm_setXmm]; dsimp only
    rw [ifp rfl, word_paddw _ _ hi]
    exact (W.ibflyW (hx i hi) (hy i hi) (hz i hi)).1
  · rw [l3 i hi]; dsimp only; rw [l2 i hi]; dsimp only; rw [w3, w13, word_psubw _ _ hi]
    exact (W.ibflyW (hx i hi) (hy i hi) (hz i hi)).2
  · refine ((((XOnly.setXmm (by simp) (XOnly.setXmm (by simp) (XOnly.setXmm (by simp)
      (XOnly.refl [.xmm3, .xmm0] s) _) _) _).trans o1).trans (o2.trans o3)).mono ?_)
    simp

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VMem`. -/
section

/-!
# ML-KEM on x86-64: polynomials as words in the working space

A polynomial stored as 256 words (`S16`), 16-byte loads of eight of its
coefficients (`lanes_load`) and stores of them (`s16_write2`), and the table
of the zetas as words (`T16`), from which `vzeta` loads the zetas of up to
four blocks (`vzeta_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The address of word `i` of the array at `p`. -/
abbrev wAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (2 * i)

/-- Word `i` of the array at `p`. -/
def wordAt (m : Mem) (p : Addr) (i : Nat) : BitVec 16 := m.readW (VG.Proof.MlKem.X86_64.wAddr p i) 16

/-- The polynomial `F` as 256 words at `p`. -/
def S16 (m : Mem) (p : Addr) (F : Poly) : Prop := ∀ i < 256, (VG.Proof.MlKem.X86_64.wordAt m p i).toNat = (F[i]!).val

/-- The 512 bytes of a polynomial as words. -/
abbrev sR (p : Addr) : Region := ⟨p, 512⟩

theorem wAddr_add (p : Addr) (j e : Nat) : VG.Proof.MlKem.X86_64.wAddr p j + BitVec.ofNat 64 (2 * e) = VG.Proof.MlKem.X86_64.wAddr p (j + e) := by
  rw [VG.Proof.MlKem.X86_64.wAddr, VG.Proof.MlKem.X86_64.wAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem lanes_load {m : Mem} {p : Addr} {F : Poly} (h : VG.Proof.MlKem.X86_64.S16 m p F) {j : Nat} (hj : j + 8 ≤ 256) :
    VG.Proof.MlKem.X86_64.Lanes (m.readW (VG.Proof.MlKem.X86_64.wAddr p j) 128) (fun e => F[j + e]!) := fun e he => by
  rw [word_readW _ _ he, VG.Proof.MlKem.X86_64.wAddr_add]; exact h _ (by bdd_omega)

/-- Word `i` after storing `x` at word `j`. -/
theorem wordAt_write128 (m : Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    VG.Proof.MlKem.X86_64.wordAt (m.writeW (VG.Proof.MlKem.X86_64.wAddr p j) x) p i = if j ≤ i ∧ i < j + 8 then word x (i - j) else VG.Proof.MlKem.X86_64.wordAt m p i := by
  split
  · rename_i h
    rw [VG.Proof.MlKem.X86_64.wordAt, show VG.Proof.MlKem.X86_64.wAddr p i = VG.Proof.MlKem.X86_64.wAddr p j + BitVec.ofNat 64 (2 * (i - j)) by
      rw [VG.Proof.MlKem.X86_64.wAddr_add, show j + (i - j) = i by bdd_omega]]
    exact readW_writeW128_16 _ _ _ (by bdd_omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)) (by decide)

/-- Two vectors stored into the words of a polynomial, with the lanes `a` and `b`. -/
theorem s16_write2 {m : Mem} {p : Addr} {P R : Poly} (hP : VG.Proof.MlKem.X86_64.S16 m p P) {j j' : Nat}
    (hj : j + 8 ≤ 256) (hj' : j' + 8 ≤ 256) (hsep : j + 8 ≤ j' ∨ j' + 8 ≤ j) {x y : BitVec 128}
    {a b : Nat → Zq} (hx : VG.Proof.MlKem.X86_64.Lanes x a) (hy : VG.Proof.MlKem.X86_64.Lanes y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 8 then a (i - j)
      else if j' ≤ i ∧ i < j' + 8 then b (i - j') else P[i]!) :
    VG.Proof.MlKem.X86_64.S16 ((m.writeW (VG.Proof.MlKem.X86_64.wAddr p j) x).writeW (VG.Proof.MlKem.X86_64.wAddr p j') y) p R := fun i hi => by
  rw [VG.Proof.MlKem.X86_64.wordAt_write128 _ _ hj' _ hi, VG.Proof.MlKem.X86_64.wordAt_write128 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact hy _ (by bdd_omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact hx _ (by bdd_omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact hP i hi

theorem sR_contains (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) : (VG.Proof.MlKem.X86_64.sR p).Contains (VG.Proof.MlKem.X86_64.wAddr p j) 16 :=
  Offset.contains_base p (by bdd_omega) (by bdd_omega)

theorem frame_write2 {m m' : Mem} {p : Addr} (hf : Frame [VG.Proof.MlKem.X86_64.sR p] m m') {j j' : Nat} (hj : j + 8 ≤ 256)
    (hj' : j' + 8 ≤ 256) (x y : BitVec 128) :
    Frame [VG.Proof.MlKem.X86_64.sR p] m ((m'.writeW (VG.Proof.MlKem.X86_64.wAddr p j) x).writeW (VG.Proof.MlKem.X86_64.wAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (VG.Proof.MlKem.X86_64.sR_contains p hj)).writeW (List.mem_singleton_self _) y
    (VG.Proof.MlKem.X86_64.sR_contains p hj')

/-! ## The table of zetas -/

/-- The 128 words `ζ^BitRev7(k) · 2¹⁶ mod q` at `p`. -/
def T16 (m : Mem) (p : Addr) : Prop := ∀ k < 128, (VG.Proof.MlKem.X86_64.wordAt m p k).toNat = (zeta k).val * 65536 % 3329

/-- Writes to the polynomial's words, 256 bytes above the table, keep it. -/
theorem T16.frame {m m' : Mem} {p : Addr} (h : VG.Proof.MlKem.X86_64.T16 m p) (hf : Frame [VG.Proof.MlKem.X86_64.sR (p + BitVec.ofNat 64 256)] m m') :
    VG.Proof.MlKem.X86_64.T16 m' p := fun k hk => by
  rw [VG.Proof.MlKem.X86_64.wordAt, hf.readW (r := ⟨p, 256⟩) (Offset.contains_base p (by bdd_omega) (by bdd_omega))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint p (by bdd_omega) (by bdd_omega))
    (by decide)]
  exact h k hk

/-- The doubleword that `pshufd` with `o` puts in place `j`. -/
def sel (o : BitVec 8) (j : Nat) : Nat := (o.extractLsb' (2 * j) 2).toNat

theorem sel_lt (o : BitVec 8) (j : Nat) : VG.Proof.MlKem.X86_64.sel o j < 4 := by unfold VG.Proof.MlKem.X86_64.sel; exact BitVec.isLt _

theorem word_shufDwords (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 8) :
    word (shufDwords a o) i = word a (2 * VG.Proof.MlKem.X86_64.sel o (i / 2) + i % 2) := by
  have hs := VG.Proof.MlKem.X86_64.sel_lt o (i / 2)
  rw [word_eq_dword _ hi, dword_shufDwords _ _ (by bdd_omega)]
  change BitVec.extractLsb' _ 16 (dword a (VG.Proof.MlKem.X86_64.sel o (i / 2))) = _
  generalize VG.Proof.MlKem.X86_64.sel o (i / 2) = t at *
  rw [word_eq_dword _ (show 2 * t + i % 2 < 8 by bdd_omega), show (2 * t + i % 2) / 2 = t by bdd_omega,
    show (2 * t + i % 2) % 2 = i % 2 by bdd_omega]

/-- The zetas that `vzeta o` leaves in `xmm13`, from the words at `wAddr zP k`. -/
theorem zeta_lanes (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + VG.Proof.MlKem.X86_64.sel o j < 128) {m : Mem}
    (ht : VG.Proof.MlKem.X86_64.T16 m zP) :
    VG.Proof.MlKem.X86_64.ZLanes (shufDwords (XBinOp.eval .punpcklwd (m.readW (VG.Proof.MlKem.X86_64.wAddr zP k) 128) (m.readW (VG.Proof.MlKem.X86_64.wAddr zP k) 128)) o)
      (fun i => zeta (k + VG.Proof.MlKem.X86_64.sel o (i / 2))) := fun i hi => by
  dsimp only
  have hs := VG.Proof.MlKem.X86_64.sel_lt o (i / 2)
  have hk' := hk (i / 2) (by bdd_omega)
  rw [VG.Proof.MlKem.X86_64.word_shufDwords _ _ hi]
  generalize VG.Proof.MlKem.X86_64.sel o (i / 2) = t at *
  rw [word_punpcklwd _ _ (by bdd_omega), ite_self, show (2 * t + i % 2) / 2 = t by bdd_omega,
    word_readW _ _ (by bdd_omega), VG.Proof.MlKem.X86_64.wAddr_add]
  exact ht _ hk'

theorem vzeta_ok (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + VG.Proof.MlKem.X86_64.sel o j < 128) {s : State}
    (h8 : s.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr zP k) (hin : InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.wAddr zP k) 16) (ht : VG.Proof.MlKem.X86_64.T16 s.mem zP) :
    WP isa (.block (vzeta o)) s fun s' =>
      VG.Proof.MlKem.X86_64.ZLanes (s'.xmm .xmm13) (fun i => zeta (k + VG.Proof.MlKem.X86_64.sel o (i / 2))) ∧ VG.Proof.MlKem.X86_64.XOnly [.xmm13] s s' := by
  simp only [vzeta, xb]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128, ea_at,
    add_ofNat_zero, h8, hin, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, by xonly⟩
  simp only [VG.Proof.MlKem.X86_64.xmm_setXmm, ite_true]
  have hs := VG.Proof.MlKem.X86_64.sel_lt o (i / 2)
  have hk' := hk (i / 2) (by bdd_omega)
  rw [VG.Proof.MlKem.X86_64.word_shufDwords _ _ hi]
  generalize VG.Proof.MlKem.X86_64.sel o (i / 2) = t at *
  rw [word_punpcklwd _ _ (by bdd_omega), ite_self, show (2 * t + i % 2) / 2 = t by bdd_omega,
    word_readW _ _ (by bdd_omega), VG.Proof.MlKem.X86_64.wAddr_add]
  exact ht _ hk'

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VLay`. -/
section

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len ≥ 8`

For any butterfly code `bf` that does what `op` does to the words of two
registers (`VBflyOk`), and any block of the specification whose butterflies do
`op` (`BlkOk`): eight butterflies of a block (`vstep`), the `len / 8` of them
of a block (`vblock_ok`), and the `128 / len` blocks of a layer (`vlay_ok`),
from the words of the polynomial at `Sp`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- Runs a block of general-purpose and SSE instructions. -/
syntax "vrunm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vrunm) => `(tactic| vrunm [])
  | `(tactic| vrunm [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
        readSrc, readSrc32, execAlu, execAlu32, State.setReg32, arithFlags_eq, ea_at, add_ofNat_zero,
        State.load128, State.store128, State.load64, State.store64, State.load32, State.store32, setReg_gpr, setReg_mem, setReg_rd, setReg_wr, setReg_cf, setReg_zf,
        setFlags_gpr, setFlags_mem, setFlags_rd, setFlags_wr, setFlags_cf, setFlags_zf, RegUpd.gpr_setXmm,
        RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.zf_setXmm, mxcsr_setXmm, xmm_setXmm,
        RegUpd.xmm_setReg, RegUpd.xmm_setFlags, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags,
        Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
        ite_false, reduceCtorEq, BitVec.sub_self, sx1, sx16, true_and, and_true, List.cons_append,
        List.nil_append, xb, xmov, $ls,*]))

/-- The code `bf` of eight butterflies does what `op` does to each pair of
words of `xmm0` and `xmm1`, with the zetas in `xmm13`, leaving the results
in `xmm0` and `xmm3`. -/
def VBflyOk (bf : List Instr) (op : Zq → Zq → Zq → Zq × Zq) : Prop :=
  ∀ s : State, VG.Proof.MlKem.X86_64.VConsts s → ∀ x y ζ : Nat → Zq, VG.Proof.MlKem.X86_64.Lanes (s.xmm .xmm0) x → VG.Proof.MlKem.X86_64.Lanes (s.xmm .xmm1) y →
    VG.Proof.MlKem.X86_64.ZLanes (s.xmm .xmm13) ζ →
    WP isa (.block bf) s fun s' => VG.Proof.MlKem.X86_64.Lanes (s'.xmm .xmm0) (fun i => (op (x i) (y i) (ζ i)).1) ∧
      VG.Proof.MlKem.X86_64.Lanes (s'.xmm .xmm3) (fun i => (op (x i) (y i) (ζ i)).2) ∧ VG.Proof.MlKem.X86_64.XOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s'

theorem vbfly_spec : VG.Proof.MlKem.X86_64.VBflyOk vbfly (fun x y z => (x + z * y, x - z * y)) :=
  fun _ hc _ _ _ hx hy hz => VG.Proof.MlKem.X86_64.vbfly_ok hc hx hy hz

theorem vibfly_spec : VG.Proof.MlKem.X86_64.VBflyOk vibfly (fun x y z => (x + y, z * (y - x))) :=
  fun _ hc _ _ _ hx hy hz => VG.Proof.MlKem.X86_64.vibfly_ok hc hx hy hz

/-- The first `t` butterflies of a block of the specification do `op` to
`(j, j + len)`. -/
structure BlkOk (blk : Poly → Nat → Nat → Nat → Nat → Poly) (op : Zq → Zq → Zq → Zq × Zq) : Prop where
  zero : ∀ f len k st, blk f len k st 0 = f
  add : ∀ f len k st t t', blk f len k st (t + t') = blk (blk f len k st t) len k (st + t) t'
  get : ∀ f len k st t, 0 < len → t ≤ len → st + len + t ≤ n → ∀ i < n,
    (blk f len k st t)[i]! = if st ≤ i ∧ i < st + t then (op f[i]! f[i + len]! (zeta k)).1
      else if st + len ≤ i ∧ i < st + len + t then (op f[i - len]! f[i]! (zeta k)).2 else f[i]!

theorem nttBlk_ok : VG.Proof.MlKem.X86_64.BlkOk nttBlockN (fun x y z => (x + z * y, x - z * y)) :=
  ⟨nttBlockN_zero, nttBlockN_add, fun f _ _ _ _ hl ht hs _ hi => nttBlockN_get' f hl ht hs hi⟩

theorem nttInvBlk_ok : VG.Proof.MlKem.X86_64.BlkOk nttInvBlockN (fun x y z => (x + y, z * (y - x))) :=
  ⟨nttInvBlockN_zero, nttInvBlockN_add, fun f _ _ _ _ hl ht hs _ hi => nttInvBlockN_get' f hl ht hs hi⟩

/-! ## A block -/

/-- The words of the polynomial, 256 bytes into the working space. -/
abbrev spW (sP : Addr) : Addr := sP + BitVec.ofNat 64 256

theorem sp_in {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {j : Nat} (hj : j + 8 ≤ 256) :
    InRegions rs (VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) j) 16 := by
  refine ⟨_, hw, ?_⟩
  rw [VG.Proof.MlKem.X86_64.wAddr, VG.Proof.MlKem.X86_64.spW, Offset.add_add]
  exact Offset.contains_base sP (by omega) (by omega)

theorem tab_in {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {k : Nat} (hk : 2 * k + 16 ≤ 1024) :
    InRegions rs (VG.Proof.MlKem.X86_64.wAddr sP k) 16 :=
  ⟨_, hw, Offset.contains_base sP (by omega) (by omega)⟩

theorem sel_zero (j : Nat) : VG.Proof.MlKem.X86_64.sel 0 j = 0 := by simp [VG.Proof.MlKem.X86_64.sel]

/-- The code of a block of a layer with `len ≥ 8`. -/
abbrev vblk (bf : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (vzeta 0 ++ ([.alu .add .r8 (.imm dz)] : List Instr)))
    (.seq (rcxLoop (len / 8) (([.movdquLoad .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len))] : List Instr) ++
        bf ++ ([.movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len)) .xmm3,
          .alu .add .rdx (.imm 16)] : List Instr)))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (2 * len))), .alu .sub .rax (.imm 1)]))

/-- Only the general-purpose registers `rs` (and the flags) changed. -/
structure GOnly (rs : List Reg) (s s' : State) : Prop where
  keep : Keep rs s s'
  mem : s'.mem = s.mem
  xmm : s'.xmm = s.xmm
  mxcsr : s'.mxcsr = s.mxcsr

/-- `GOnly` of a chain of `setReg` and `setFlags`. -/
macro "gonly" : tactic => `(tactic| exact ⟨⟨fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false], rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem GOnly.consts {rs : List Reg} {s s' : State} (h : VG.Proof.MlKem.X86_64.GOnly rs s s') (hc : VG.Proof.MlKem.X86_64.VConsts s) : VG.Proof.MlKem.X86_64.VConsts s' :=
  ⟨by rw [h.xmm]; exact hc.q, by rw [h.xmm]; exact hc.qinv⟩

/-- `rcxLoop N body`: the body runs `N` times, from a state that the `mov`
of the count changed in `rcx` only. -/
theorem wp_rcxLoop {body : List Instr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 31) (Inv : Nat → State → Prop)
    {s₀ : State} (h0 : ∀ s, VG.Proof.MlKem.X86_64.GOnly [.rcx] s₀ s → s.gpr .rcx = BitVec.ofNat 64 N → Inv 0 s)
    (hbody : ∀ i < N, ∀ s, Inv i s →
      WP isa (.block (body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' => Inv (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) :
    WP isa (rcxLoop N body) s₀ (Inv N) := by
  refine WP.seq (WP.mono (Q := fun (s : State) => VG.Proof.MlKem.X86_64.GOnly [.rcx] s₀ s ∧ s.gpr .rcx = BitVec.ofNat 64 N)
    (by vrunm; exact ⟨by gonly, by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega⟩) fun s ⟨o, hc⟩ => ?_)
  exact wp_countdown (by omega) hN Inv (fun i hi s hI _ => hbody i hi s hI) (fun _ h => h) (h0 s o hc) hc

/-- The first `b` blocks of the layer with `len`, block `c` with the zeta
`zeta (zi c)`. -/
def layF (blk : Poly → Nat → Nat → Nat → Nat → Poly) (F : Poly) (len : Nat) (zi : Nat → Nat) (b : Nat) :
    Poly :=
  (List.range b).foldl (fun f c => blk f len (zi c) (2 * len * c) len) F

/-- The facts a block keeps. -/
structure BInv (sP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [VG.Proof.MlKem.X86_64.sR (VG.Proof.MlKem.X86_64.spW sP)] s₀.mem s.mem
  consts : VG.Proof.MlKem.X86_64.VConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInv.trans {sP : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.X86_64.BInv sP s₁ s₂) (h₂ : VG.Proof.MlKem.X86_64.BInv sP s₂ s₃) : VG.Proof.MlKem.X86_64.BInv sP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

/-! ## Eight butterflies -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VG.Proof.MlKem.X86_64.VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : VG.Proof.MlKem.X86_64.BlkOk blk op)
include hbf hblk

/-- The body of the loop over the vectors of a block. -/
abbrev vbody (bf : List Instr) (len : Nat) : List Instr :=
  ([.movdquLoad .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len))] : List Instr) ++ bf ++
    ([.movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len)) .xmm3, .alu .add .rdx (.imm 16)] : List Instr) ++
    ([.alu .sub .rcx (.imm 1)] : List Instr)

theorem vstep {Sp : Addr} {len st u k : Nat} (hl : 0 < len) (hs : st + 2 * len ≤ 256) (hu : 8 * u + 8 ≤ len)
    {G : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hz : VG.Proof.MlKem.X86_64.ZLanes (s.xmm .xmm13) (fun _ => zeta k))
    (hdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr Sp (st + 8 * u)) (hS : VG.Proof.MlKem.X86_64.S16 s.mem Sp (blk G len k st (8 * u)))
    (hin : ∀ j, j + 8 ≤ 256 → InRegions s.wr (VG.Proof.MlKem.X86_64.wAddr Sp j) 16) :
    WP isa (.block (VG.Proof.MlKem.X86_64.vbody bf len)) s fun s' =>
      VG.Proof.MlKem.X86_64.S16 s'.mem Sp (blk G len k st (8 * (u + 1))) ∧ s'.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr Sp (st + 8 * (u + 1)) ∧
        Frame [VG.Proof.MlKem.X86_64.sR Sp] s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.VConsts s' ∧ s'.xmm .xmm13 = s.xmm .xmm13 ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : st + 8 * u + 8 ≤ 256 := by omega
  have j1 : st + 8 * u + len + 8 ≤ 256 := by omega
  have a1 : VG.Proof.MlKem.X86_64.wAddr Sp (st + 8 * u) + BitVec.ofNat 64 (2 * len) = VG.Proof.MlKem.X86_64.wAddr Sp (st + 8 * u + len) := VG.Proof.MlKem.X86_64.wAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.wAddr Sp (st + 8 * u)) 16 := by
    obtain ⟨r, hr, hc⟩ := hin _ j0; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have r1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.wAddr Sp (st + 8 * u + len)) 16 := by
    obtain ⟨r, hr, hc⟩ := hin _ j1; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have w0 := hin _ j0
  have w1 := hin _ j1
  rw [VG.Proof.MlKem.X86_64.vbody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  vrunm [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  have hx := VG.Proof.MlKem.X86_64.lanes_load hS j0
  have hy := VG.Proof.MlKem.X86_64.lanes_load hS j1
  refine WP.mono (hbf _ ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _)
    (fun e => (blk G len k st (8 * u))[st + 8 * u + e]!) (fun e => (blk G len k st (8 * u))[st + 8 * u + len + e]!)
    (fun _ => zeta k) (by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; exact hx) (by rw [VG.Proof.MlKem.X86_64.xmm_setXmm]; exact hy)
    (by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; exact hz)) fun s2 ⟨l0, l3, o2⟩ => ?_
  have c2 := o2.consts ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _) (by decide)
    (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨o2.rd, o2.wr⟩
  have x2 : s2.mxcsr = s.mxcsr := o2.mxcsr
  have z2 : s2.xmm .xmm13 = s.xmm .xmm13 := by rw [o2.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm, VG.Proof.MlKem.X86_64.xmm_setXmm]; rfl
  vrunm [g2, m2, e2.1, e2.2, hdx, a1, w0, w1, x2]
  refine ⟨?_, ?_, ?_, ⟨c2.q, c2.qinv⟩, z2, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · refine VG.Proof.MlKem.X86_64.s16_write2 hS j0 j1 (by omega) l0 l3 fun i hi => ?_
    rw [show 8 * (u + 1) = 8 * u + 8 by omega, hblk.add, hblk.get _ _ _ _ _ hl (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    by_cases c1 : st + 8 * u ≤ i ∧ i < st + 8 * u + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c1), ite_eq_left_of_eq_true _ _ (eq_true c1),
        show st + 8 * u + (i - (st + 8 * u)) = i by omega,
        show st + 8 * u + len + (i - (st + 8 * u)) = i + len by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c1)]
      by_cases c2 : st + 8 * u + len ≤ i ∧ i < st + 8 * u + len + 8
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c2), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          show st + 8 * u + (i - (st + 8 * u + len)) = i - len by omega,
          show st + 8 * u + len + (i - (st + 8 * u + len)) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, VG.Proof.MlKem.X86_64.wAddr_add,
      show st + 8 * u + 8 = st + 8 * (u + 1) by omega]
  · exact VG.Proof.MlKem.X86_64.frame_write2 (Frame.refl _ _) j0 j1 _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

theorem vblock_ok {sP : Addr} {len st kz : Nat} (h8 : 8 ≤ len) (hl8 : len % 8 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz < 128) (dz : BitVec 32) {G : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s)
    (hdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) st) (h8r : s.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP kz) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) G)
    (hT : VG.Proof.MlKem.X86_64.T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (VG.Proof.MlKem.X86_64.vblk bf len dz) s fun s' => VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (blk G len kz st len) ∧
      s'.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (st + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ VG.Proof.MlKem.X86_64.BInv sP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vzeta_ok 0 (k := kz) (fun j _ => by rw [VG.Proof.MlKem.X86_64.sel_zero]; omega) h8r
    (VG.Proof.MlKem.X86_64.tab_in (List.mem_append_right _ hw) (by omega)) hT) fun s1 ⟨z1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      VG.Proof.MlKem.X86_64.GOnly [.r8] s1 s2)
    (by vrunm [g1]; gonly)
    fun s2 ⟨h82, o2⟩ => ?_
  have c2 := o2.consts (o1.consts hc (by decide) (by decide))
  have z2 : VG.Proof.MlKem.X86_64.ZLanes (s2.xmm .xmm13) (fun _ => zeta kz) := by
    rw [o2.xmm]; intro i hi; rw [z1 i hi]; dsimp only; rw [VG.Proof.MlKem.X86_64.sel_zero, Nat.add_zero]
  have dx2 : s2.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR sP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hw
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoop (N := len / 8) (by omega) (by omega)
    (fun u w => VG.Proof.MlKem.X86_64.S16 w.mem (VG.Proof.MlKem.X86_64.spW sP) (blk G len kz st (8 * u)) ∧ w.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (st + 8 * u) ∧
      VG.Proof.MlKem.X86_64.VConsts w ∧ w.xmm .xmm13 = s2.xmm .xmm13 ∧ Keep [.rcx, .rdx] s2 w ∧ Frame [VG.Proof.MlKem.X86_64.sR (VG.Proof.MlKem.X86_64.spW sP)] s2.mem w.mem ∧
      w.mxcsr = s2.mxcsr)
    (fun w o hc => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      o.consts c2, by rw [o.xmm], o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hk', hf', hx'⟩ => WP.mono (VG.Proof.MlKem.X86_64.vstep hbf hblk (by omega) hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl8); omega) hc' (by rw [hz']; exact z2) hdx' hS'
        (fun j hj => VG.Proof.MlKem.X86_64.sp_in (by rw [hk'.2.2]; exact hw2) hj))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', by rw [hz'', hz'], (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩,
          hcx, hzf⟩)) fun w ⟨hS3, hdx3, hc3, hz3, hk3, hf3, hx3⟩ => ?_)
  rw [show 8 * (len / 8) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl8)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [hk3.gpr (by decide), h82]
  vrunm [hdx3, sx_ofNat (show 2 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [VG.Proof.MlKem.X86_64.wAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
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

theorem vlay_ok {sP : Addr} {len k : Nat} (hlen : len ∈ [8, 16, 32, 64, 128]) (dz : BitVec 32)
    (zi : Nat → Nat) (hz0 : zi 0 = k) (hzi : ∀ c < 128 / len, zi c < 128)
    (hstep : ∀ c < 128 / len, VG.Proof.MlKem.X86_64.wAddr sP (zi c) + BitVec.signExtend 64 dz = VG.Proof.MlKem.X86_64.wAddr sP (zi (c + 1)))
    {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hsi : s.gpr .rsi = sP) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay bf len k dz) s fun s' => VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F len zi (128 / len)) ∧
      VG.Proof.MlKem.X86_64.BInv sP s s' := by
  have hl : 8 ≤ len ∧ len % 8 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h8, hl8, hl128, hcov, hpos, h16⟩ := hl
  have hk : k < 128 := hz0 ▸ hzi 0 hpos
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = VG.Proof.MlKem.X86_64.spW sP ∧ w.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP k ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ VG.Proof.MlKem.X86_64.GOnly [.rdx, .r8, .rax] s w)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * k < 2 ^ 31 by omega), hsi]
      refine ⟨?_, by gonly⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o⟩ => ?_)
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => VG.Proof.MlKem.X86_64.S16 u.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F len zi c) ∧ u.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (2 * len * c) ∧
      u.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP (zi c) ∧ VG.Proof.MlKem.X86_64.BInv sP w u ∧ VG.Proof.MlKem.X86_64.T16 u.mem sP)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, VG.Proof.MlKem.X86_64.wAddr, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, hz0], ⟨Keep.refl _ _, Frame.refl _ _, o.consts hc, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (VG.Proof.MlKem.X86_64.vblock_ok hbf hblk h8 hl8 hl128 hs (hzi c hc) dz hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hw')) fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [VG.Proof.MlKem.X86_64.layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', h8', hstep c hc], hb'.trans hb'', hT'.frame hb''.frame⟩, hax'', hzf''⟩

end

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VLay42`. -/
section

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len` = 4 and 2

The layer with `len = 4` runs two blocks at a time (`vstep4`): the lower
halves of their coefficients gathered into `xmm0` and the upper ones into
`xmm1` by `punpcklqdq` and `punpckhqdq`, and back. The layer with `len = 2`
runs four blocks at a time (`vstep2`): their pairs gathered by `pshufd` and
`punpck{l,h}qdq`, and interleaved back by `punpck{l,h}dq`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem word_punpckldq (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .punpckldq a b) i =
      if i / 2 % 2 = 0 then word a (2 * (i / 4) + i % 2) else word b (2 * (i / 4) + i % 2) := by
  rw [dword_punpckldq, word_eq_dword _ hi]
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, ite_true,
    ite_false, Nat.reduceEqDiff, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    word_eq_dword]

theorem word_punpckhdq (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .punpckhdq a b) i =
      if i / 2 % 2 = 0 then word a (4 + 2 * (i / 4) + i % 2) else word b (4 + 2 * (i / 4) + i % 2) := by
  rw [dword_punpckhdq, word_eq_dword _ hi]
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, ite_true,
    ite_false, Nat.reduceEqDiff, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    word_eq_dword]

/-- The general-purpose registers but `rs`, memory, the permissions and
MXCSR are as they were. -/
structure GKeep (rs : List Reg) (s s' : State) : Prop where
  keep : Keep rs s s'
  mem : s'.mem = s.mem
  mxcsr : s'.mxcsr = s.mxcsr

theorem sel_d8 (j : Nat) (hj : j < 4) : VG.Proof.MlKem.X86_64.sel 0xD8 j = [0, 2, 1, 3][j]! := by
  rcases (by bdd_omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The words of `X` that `pshufd` with `0xD8` puts in the lower half, then in the upper half. -/
theorem word_d8 (x : BitVec 128) {e : Nat} (he : e < 8) :
    word (shufDwords x 0xD8) e = word x (if e < 4 then 4 * (e / 2) + e % 2 else 4 * ((e - 4) / 2) + 2 + e % 2) := by
  rw [VG.Proof.MlKem.X86_64.word_shufDwords _ _ he, VG.Proof.MlKem.X86_64.sel_d8 _ (by bdd_omega)]
  congr 1
  rcases (by bdd_omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The layer with `len = 4` -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VG.Proof.MlKem.X86_64.VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : VG.Proof.MlKem.X86_64.BlkOk blk op)
include hbf hblk

/-- The loads, the zetas and the gathering of the lower and upper halves. -/
abbrev pre4 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  ([.movdquLoad .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .movdquLoad .xmm1 (VG.Impl.MlKem.X86_64.at_ .rdx 16)] : List Instr) ++ vzeta o ++
    ([.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
      xmov .xmm1 .xmm2] : List Instr)

/-- The interleaving back, the stores and the counts. -/
abbrev post4 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
    .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

theorem vstep4 {sP : Addr} {i kz : Nat} (hi : i < 16) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : ∀ j < 4, kz + VG.Proof.MlKem.X86_64.sel o j < 128) (hsel : ∀ e < 8, kz + VG.Proof.MlKem.X86_64.sel o (e / 2) = zi (2 * i + e / 4))
    {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i))
    (h8 : s.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP kz) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 4 zi (2 * i))) (hT : VG.Proof.MlKem.X86_64.T16 s.mem sP)
    (hw : pR sP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlKem.X86_64.pre4 o dz ++ (bf ++ VG.Proof.MlKem.X86_64.post4))) s fun s' =>
      VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 4 zi (2 * (i + 1))) ∧ s'.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.MlKem.X86_64.BInv sP s s' := by
  have j0 : 16 * i + 8 ≤ 256 := by bdd_omega
  have j1 : 16 * i + 8 + 8 ≤ 256 := by bdd_omega
  have a1 : VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i) + BitVec.ofNat 64 16 = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i + 8) := VG.Proof.MlKem.X86_64.wAddr_add _ _ 8
  have r0 := VG.Proof.MlKem.X86_64.sp_in (List.mem_append_right s.rd hw) j0
  have r1 := VG.Proof.MlKem.X86_64.sp_in (List.mem_append_right s.rd hw) j1
  have rz := VG.Proof.MlKem.X86_64.tab_in (List.mem_append_right s.rd hw) (k := kz) (by have := hk 0 (by decide); omega)
  generalize hG : VG.Proof.MlKem.X86_64.layF blk F 4 zi (2 * i) = G at hS
  have lx := VG.Proof.MlKem.X86_64.lanes_load hS j0
  have ly := VG.Proof.MlKem.X86_64.lanes_load hS j1
  have lz := VG.Proof.MlKem.X86_64.zeta_lanes o hk hT
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => VG.Proof.MlKem.X86_64.Lanes (s1.xmm .xmm0) (fun e => G[16 * i + e + 4 * (e / 4)]!) ∧
      VG.Proof.MlKem.X86_64.Lanes (s1.xmm .xmm1) (fun e => G[16 * i + 4 + e + 4 * (e / 4)]!) ∧
      VG.Proof.MlKem.X86_64.ZLanes (s1.xmm .xmm13) (fun e => zeta (zi (2 * i + e / 4))) ∧ VG.Proof.MlKem.X86_64.VConsts s1 ∧
      s1.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ VG.Proof.MlKem.X86_64.GKeep [.r8] s s1) ?_
    fun s1 ⟨l0, l1, l13, c1, h81, o1⟩ => ?_
  · simp only [VG.Proof.MlKem.X86_64.pre4, vzeta, xmov, xb]
    vrunm [hdx, a1, r0, r1, rz, h8]
    refine ⟨?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    rotate_left 3
    · constructor <;>
        simp only [VG.Proof.MlKem.X86_64.xmm_setXmm, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, reduceCtorEq, ite_false] <;>
        [exact hc.q; exact hc.qinv]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    all_goals try simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, VG.Proof.MlKem.X86_64.mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags]
    · intro e he
      rw [word_punpcklqdq _ _ he]
      split
      · rw [lx e he]; dsimp only; rw [show 16 * i + e + 4 * (e / 4) = 16 * i + e by bdd_omega]
      · rw [ly (e - 4) (by bdd_omega)]; dsimp only
        rw [show 16 * i + e + 4 * (e / 4) = 16 * i + 8 + (e - 4) by bdd_omega]
    · intro e he
      rw [word_movdqa, word_punpckhqdq _ _ he, word_movdqa]
      split
      · rw [lx (4 + e) (by bdd_omega)]; dsimp only
        rw [show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + (4 + e) by bdd_omega]
      · rw [ly e he]; dsimp only; rw [show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + 8 + e by bdd_omega]
    · intro e he
      rw [lz e he]; dsimp only; rw [hsel e he]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1.keep.2.1], by rw [o2.wr, o1.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  have w0 := VG.Proof.MlKem.X86_64.sp_in hw j0
  have w1 := VG.Proof.MlKem.X86_64.sp_in hw j1
  have c2 := o2.consts c1 (by decide) (by decide)
  simp only [VG.Proof.MlKem.X86_64.post4, xmov, xb]
  vrunm [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, VG.Proof.MlKem.X86_64.wAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the words stored
    refine VG.Proof.MlKem.X86_64.s16_write2 hS j0 j1 (by bdd_omega)
      (a := fun e => if e < 4 then (op G[16 * i + e]! G[16 * i + 4 + e]! (zeta (zi (2 * i)))).1
        else (op G[16 * i + (e - 4)]! G[16 * i + 4 + (e - 4)]! (zeta (zi (2 * i)))).2)
      (b := fun e => if e < 4 then (op G[16 * i + 8 + e]! G[16 * i + 12 + e]! (zeta (zi (2 * i + 1)))).1
        else (op G[16 * i + 8 + (e - 4)]! G[16 * i + 12 + (e - 4)]! (zeta (zi (2 * i + 1)))).2)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [word_punpcklqdq _ _ he]
      split
      · rw [a0 e he]; dsimp only
        rw [ite_eq_left (by bdd_omega), show 16 * i + e + 4 * (e / 4) = 16 * i + e by bdd_omega,
          show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + 4 + e by bdd_omega, show 2 * i + e / 4 = 2 * i by bdd_omega]
      · rw [a3 (e - 4) (by bdd_omega)]; dsimp only
        rw [ite_eq_right (by bdd_omega), show 16 * i + (e - 4) + 4 * ((e - 4) / 4) = 16 * i + (e - 4) by bdd_omega,
          show 16 * i + 4 + (e - 4) + 4 * ((e - 4) / 4) = 16 * i + 4 + (e - 4) by bdd_omega,
          show 2 * i + (e - 4) / 4 = 2 * i by bdd_omega]
    · rw [word_punpckhqdq _ _ he, word_movdqa]
      split
      · rw [a0 (4 + e) (by bdd_omega)]; dsimp only
        rw [ite_eq_left (by bdd_omega), show 16 * i + (4 + e) + 4 * ((4 + e) / 4) = 16 * i + 8 + e by bdd_omega,
          show 16 * i + 4 + (4 + e) + 4 * ((4 + e) / 4) = 16 * i + 12 + e by bdd_omega,
          show 2 * i + (4 + e) / 4 = 2 * i + 1 by bdd_omega]
      · rw [a3 e he]; dsimp only
        rw [ite_eq_right (by bdd_omega), show 16 * i + e + 4 * (e / 4) = 16 * i + 8 + (e - 4) by bdd_omega,
          show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + 12 + (e - 4) by bdd_omega,
          show 2 * i + e / 4 = 2 * i + 1 by bdd_omega]
    · -- the specification: two blocks
      rw [← hG, show 2 * (i + 1) = 2 * i + 1 + 1 by bdd_omega, VG.Proof.MlKem.X86_64.layF, foldl_range_succ, foldl_range_succ, ← VG.Proof.MlKem.X86_64.layF,
        hG, show 2 * 4 * (2 * i) = 16 * i by bdd_omega, show 2 * 4 * (2 * i + 1) = 16 * i + 8 by bdd_omega]
      have hn : ∀ j, j < 256 → j < n := fun j h => by rw [n_eq]; exact h
      rw [hblk.get _ _ _ _ _ (by decide) (by decide) (by rw [n_eq]; omega) _ (hn j hj)]
      have p2 := fun j (h : j < 256) => hblk.get G 4 (zi (2 * i)) (16 * i) 4 (by decide) (by decide)
        (by rw [n_eq]; omega) j (hn j h)
      rcases (by bdd_omega : j < 16 * i ∨ (16 * i ≤ j ∧ j < 16 * i + 4) ∨ (16 * i + 4 ≤ j ∧ j < 16 * i + 8) ∨
          (16 * i + 8 ≤ j ∧ j < 16 * i + 12) ∨ (16 * i + 12 ≤ j ∧ j < 16 * i + 16) ∨ 16 * i + 16 ≤ j) with
        h | h | h | h | h | h
      · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right, p2 j hj]
      · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 16 * i + (j - 16 * i) = j by bdd_omega, show 16 * i + 4 + (j - 16 * i) = j + 4 by bdd_omega]
      · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 16 * i + (j - 16 * i - 4) = j - 4 by bdd_omega, show 16 * i + 4 + (j - 16 * i - 4) = j by bdd_omega]
      · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j + 4) (by bdd_omega)]
        rw [show 16 * i + 8 + (j - (16 * i + 8)) = j by bdd_omega,
          show 16 * i + 12 + (j - (16 * i + 8)) = j + 4 by bdd_omega]
      · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j - 4) (by bdd_omega)]
        rw [show 16 * i + 8 + (j - (16 * i + 8) - 4) = j - 4 by bdd_omega,
          show 16 * i + 12 + (j - (16 * i + 8) - 4) = j by bdd_omega]
      · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right, p2 j hj]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, VG.Proof.MlKem.X86_64.frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, VG.Proof.MlKem.X86_64.xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, VG.Proof.MlKem.X86_64.xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv


omit hbf hblk in
/-- The prologue of the layers with `len` = 4 and 2. -/
theorem vpre42 {sP : Addr} (k : Nat) (hk : k < 128) {s : State} (hsi : s.gpr .rsi = sP) :
    WP isa (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * k))) s fun w =>
      w.gpr .rdx = VG.Proof.MlKem.X86_64.spW sP ∧ w.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP k ∧ VG.Proof.MlKem.X86_64.GOnly [.rdx, .r8] s w := by
  simp only [leaR, oS]
  vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * k < 2 ^ 31 by bdd_omega), hsi]
  gonly

theorem vlay4_ok {sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 16, ∀ j < 4, kz i + VG.Proof.MlKem.X86_64.sel o j < 128)
    (hsel : ∀ i < 16, ∀ e < 8, kz i + VG.Proof.MlKem.X86_64.sel o (e / 2) = zi (2 * i + e / 4))
    (hstep : ∀ i < 16, VG.Proof.MlKem.X86_64.wAddr sP (kz i) + BitVec.signExtend 64 dz = VG.Proof.MlKem.X86_64.wAddr sP (kz (i + 1)))
    {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hsi : s.gpr .rsi = sP) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 bf k o dz) s fun s' => VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 4 zi 32) ∧ VG.Proof.MlKem.X86_64.BInv sP s s' := by
  have hk0 : k < 128 := by have := hk 0 (by decide) 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.vpre42 k hk0 hsi)
    fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoop (N := 16) (by decide) (by decide)
    (fun i u => VG.Proof.MlKem.X86_64.S16 u.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 4 zi (2 * i)) ∧ u.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i) ∧
      u.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP (kz i) ∧ VG.Proof.MlKem.X86_64.BInv sP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, VG.Proof.MlKem.X86_64.wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ou.consts (og.consts hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : VG.Proof.MlKem.X86_64.T16 u.mem sP := (by rw [og.mem]; exact hT : T16 w.mem sP).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show VG.Proof.MlKem.X86_64.pre4 o dz ++ bf ++ [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
      .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      ([.alu .sub .rcx (.imm 1)] : List Instr) = VG.Proof.MlKem.X86_64.pre4 o dz ++ (bf ++ VG.Proof.MlKem.X86_64.post4) by simp [List.append_assoc]]
  exact WP.mono (VG.Proof.MlKem.X86_64.vstep4 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩


/-! ## The layer with `len = 2` -/

/-- The loads, the zetas and the gathering of the pairs. -/
abbrev pre2 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  ([.movdquLoad .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .movdquLoad .xmm2 (VG.Impl.MlKem.X86_64.at_ .rdx 16)] : List Instr) ++ vzeta o ++
    ([.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2] : List Instr)

/-- The interleaving back, the stores and the counts. -/
abbrev post2 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
    .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

omit hbf in
/-- Each coefficient after the first `b` blocks of the layer with `len = 2`. -/
theorem layF2_get (F : Poly) (zi : Nat → Nat) {b : Nat} (hb : b ≤ 64) {j : Nat} (hj : j < 256) :
    (VG.Proof.MlKem.X86_64.layF blk F 2 zi b)[j]! = if j < 4 * b then
      (if j % 4 < 2 then (op F[j]! F[j + 2]! (zeta (zi (j / 4)))).1
        else (op F[j - 2]! F[j]! (zeta (zi (j / 4)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by bdd_omega)]; rfl
  | succ b ih =>
    rw [VG.Proof.MlKem.X86_64.layF, foldl_range_succ, ← VG.Proof.MlKem.X86_64.layF,
      hblk.get _ 2 _ _ 2 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2 * 2 * b ≤ j ∧ j < 2 * 2 * b + 2
    · rw [ite_eq_left h1, ih (by bdd_omega) hj, ih (by bdd_omega) (by bdd_omega), show j / 4 = b by bdd_omega]
      simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2 * 2 * b + 2 ≤ j ∧ j < 2 * 2 * b + 2 + 2
      · rw [ite_eq_left h2, ih (by bdd_omega) (by bdd_omega), ih (by bdd_omega) hj, show j / 4 = b by bdd_omega]
        simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right]
      · rw [ite_eq_right h2, ih (by bdd_omega) hj]
        by_cases h3 : j < 4 * b <;> simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right]

theorem vstep2 {sP : Addr} {i kz : Nat} (hi : i < 16) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : ∀ j < 4, kz + VG.Proof.MlKem.X86_64.sel o j < 128) (hsel : ∀ e < 8, kz + VG.Proof.MlKem.X86_64.sel o (e / 2) = zi (4 * i + e / 2))
    {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i))
    (h8 : s.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP kz) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 2 zi (4 * i))) (hT : VG.Proof.MlKem.X86_64.T16 s.mem sP)
    (hw : pR sP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlKem.X86_64.pre2 o dz ++ (bf ++ VG.Proof.MlKem.X86_64.post2))) s fun s' =>
      VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 2 zi (4 * (i + 1))) ∧ s'.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.MlKem.X86_64.BInv sP s s' := by
  have j0 : 16 * i + 8 ≤ 256 := by bdd_omega
  have j1 : 16 * i + 8 + 8 ≤ 256 := by bdd_omega
  have a1 : VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i) + BitVec.ofNat 64 16 = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i + 8) := VG.Proof.MlKem.X86_64.wAddr_add _ _ 8
  have r0 := VG.Proof.MlKem.X86_64.sp_in (List.mem_append_right s.rd hw) j0
  have r1 := VG.Proof.MlKem.X86_64.sp_in (List.mem_append_right s.rd hw) j1
  have rz := VG.Proof.MlKem.X86_64.tab_in (List.mem_append_right s.rd hw) (k := kz) (by have := hk 0 (by decide); omega)
  generalize hG : VG.Proof.MlKem.X86_64.layF blk F 2 zi (4 * i) = G at hS
  have lx := VG.Proof.MlKem.X86_64.lanes_load hS j0
  have ly := VG.Proof.MlKem.X86_64.lanes_load hS j1
  have lz := VG.Proof.MlKem.X86_64.zeta_lanes o hk hT
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => VG.Proof.MlKem.X86_64.Lanes (s1.xmm .xmm0) (fun e => G[16 * i + 4 * (e / 2) + e % 2]!) ∧
      VG.Proof.MlKem.X86_64.Lanes (s1.xmm .xmm1) (fun e => G[16 * i + 4 * (e / 2) + 2 + e % 2]!) ∧
      VG.Proof.MlKem.X86_64.ZLanes (s1.xmm .xmm13) (fun e => zeta (zi (4 * i + e / 2))) ∧ VG.Proof.MlKem.X86_64.VConsts s1 ∧
      s1.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ VG.Proof.MlKem.X86_64.GKeep [.r8] s s1) ?_
    fun s1 ⟨l0, l1, l13, c1, h81, o1⟩ => ?_
  · simp only [VG.Proof.MlKem.X86_64.pre2, vzeta, xmov, xb]
    vrunm [hdx, a1, r0, r1, rz, h8]
    refine ⟨?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    rotate_left 3
    · constructor <;>
        simp only [VG.Proof.MlKem.X86_64.xmm_setXmm, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, reduceCtorEq, ite_false] <;>
        [exact hc.q; exact hc.qinv]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    all_goals try simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, VG.Proof.MlKem.X86_64.mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags]
    · intro e he
      rw [word_punpcklqdq _ _ he]
      split
      · rw [VG.Proof.MlKem.X86_64.word_d8 _ he, ite_eq_left (by bdd_omega), lx _ (by bdd_omega)]; dsimp only
        rw [show 16 * i + (4 * (e / 2) + e % 2) = 16 * i + 4 * (e / 2) + e % 2 by bdd_omega]
      · rw [VG.Proof.MlKem.X86_64.word_d8 _ (by bdd_omega), ite_eq_left (by bdd_omega), ly _ (by bdd_omega)]; dsimp only
        rw [show 16 * i + 8 + (4 * ((e - 4) / 2) + (e - 4) % 2) = 16 * i + 4 * (e / 2) + e % 2 by bdd_omega]
    · intro e he
      rw [word_punpckhqdq _ _ he]
      simp only [word_movdqa]
      split
      · rw [VG.Proof.MlKem.X86_64.word_d8 _ (by bdd_omega), ite_eq_right (by bdd_omega), lx _ (by bdd_omega)]; dsimp only
        rw [show 16 * i + (4 * ((4 + e - 4) / 2) + 2 + (4 + e) % 2) = 16 * i + 4 * (e / 2) + 2 + e % 2 by bdd_omega]
      · rw [VG.Proof.MlKem.X86_64.word_d8 _ he, ite_eq_right (by bdd_omega), ly _ (by bdd_omega)]; dsimp only
        rw [show 16 * i + 8 + (4 * ((e - 4) / 2) + 2 + e % 2) = 16 * i + 4 * (e / 2) + 2 + e % 2 by bdd_omega]
    · intro e he
      rw [lz e he]; dsimp only; rw [hsel e he]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1.keep.2.1], by rw [o2.wr, o1.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  have w0 := VG.Proof.MlKem.X86_64.sp_in hw j0
  have w1 := VG.Proof.MlKem.X86_64.sp_in hw j1
  have c2 := o2.consts c1 (by decide) (by decide)
  simp only [VG.Proof.MlKem.X86_64.post2, xmov, xb]
  vrunm [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  have lg : ∀ b, b ≤ 64 → ∀ j, j < 256 → _ := fun b hb j hj => VG.Proof.MlKem.X86_64.layF2_get hblk F zi (b := b) hb (j := j) hj
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, VG.Proof.MlKem.X86_64.wAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the words stored
    refine VG.Proof.MlKem.X86_64.s16_write2 hS j0 j1 (by bdd_omega)
      (a := fun e => (VG.Proof.MlKem.X86_64.layF blk F 2 zi (4 * (i + 1)))[16 * i + e]!)
      (b := fun e => (VG.Proof.MlKem.X86_64.layF blk F 2 zi (4 * (i + 1)))[16 * i + 8 + e]!)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [VG.Proof.MlKem.X86_64.word_punpckldq _ _ he]
      split
      · rw [a0 (2 * (e / 4) + e % 2) (by bdd_omega)]; dsimp only
        rw [show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + (2 * (e / 4) + e % 2) % 2 = 16 * i + e by bdd_omega,
          show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + 2 + (2 * (e / 4) + e % 2) % 2 = 16 * i + e + 2 by bdd_omega,
          show 4 * i + (2 * (e / 4) + e % 2) / 2 = (16 * i + e) / 4 by bdd_omega, ← hG]
        simp (disch := bdd_omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (2 * (e / 4) + e % 2) (by bdd_omega)]; dsimp only
        rw [show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + (2 * (e / 4) + e % 2) % 2 = 16 * i + e - 2 by bdd_omega,
          show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + 2 + (2 * (e / 4) + e % 2) % 2 = 16 * i + e by bdd_omega,
          show 4 * i + (2 * (e / 4) + e % 2) / 2 = (16 * i + e) / 4 by bdd_omega, ← hG]
        simp (disch := bdd_omega) only [lg, ite_eq_left, ite_eq_right]
    · rw [VG.Proof.MlKem.X86_64.word_punpckhdq _ _ he]
      simp only [word_movdqa]
      split
      · rw [a0 (4 + 2 * (e / 4) + e % 2) (by bdd_omega)]; dsimp only
        rw [show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + (4 + 2 * (e / 4) + e % 2) % 2 = 16 * i + 8 + e by
            omega,
          show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + 2 + (4 + 2 * (e / 4) + e % 2) % 2 =
            16 * i + 8 + e + 2 by bdd_omega,
          show 4 * i + (4 + 2 * (e / 4) + e % 2) / 2 = (16 * i + 8 + e) / 4 by bdd_omega, ← hG]
        simp (disch := bdd_omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (4 + 2 * (e / 4) + e % 2) (by bdd_omega)]; dsimp only
        rw [show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + (4 + 2 * (e / 4) + e % 2) % 2 =
            16 * i + 8 + e - 2 by bdd_omega,
          show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + 2 + (4 + 2 * (e / 4) + e % 2) % 2 = 16 * i + 8 + e by
            omega,
          show 4 * i + (4 + 2 * (e / 4) + e % 2) / 2 = (16 * i + 8 + e) / 4 by bdd_omega, ← hG]
        simp (disch := bdd_omega) only [lg, ite_eq_left, ite_eq_right]
    · rcases (by bdd_omega : (16 * i ≤ j ∧ j < 16 * i + 8) ∨ (16 * i + 8 ≤ j ∧ j < 16 * i + 16) ∨
          j < 16 * i ∨ 16 * i + 16 ≤ j) with h | h | h | h
      · rw [ite_eq_left h, show 16 * i + (j - 16 * i) = j by bdd_omega]
      · rw [ite_eq_right (by bdd_omega), ite_eq_left h, show 16 * i + 8 + (j - (16 * i + 8)) = j by bdd_omega]
      · rw [ite_eq_right (by bdd_omega), ite_eq_right (by bdd_omega), ← hG]
        simp (disch := bdd_omega) only [lg, ite_eq_left]
      · rw [ite_eq_right (by bdd_omega), ite_eq_right (by bdd_omega), ← hG]
        simp (disch := bdd_omega) only [lg, ite_eq_left, ite_eq_right]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, VG.Proof.MlKem.X86_64.frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, VG.Proof.MlKem.X86_64.xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, VG.Proof.MlKem.X86_64.xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv



theorem vlay2_ok {sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 16, ∀ j < 4, kz i + VG.Proof.MlKem.X86_64.sel o j < 128)
    (hsel : ∀ i < 16, ∀ e < 8, kz i + VG.Proof.MlKem.X86_64.sel o (e / 2) = zi (4 * i + e / 2))
    (hstep : ∀ i < 16, VG.Proof.MlKem.X86_64.wAddr sP (kz i) + BitVec.signExtend 64 dz = VG.Proof.MlKem.X86_64.wAddr sP (kz (i + 1)))
    {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hsi : s.gpr .rsi = sP) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 bf k o dz) s fun s' => VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 2 zi 64) ∧ VG.Proof.MlKem.X86_64.BInv sP s s' := by
  have hk0 : k < 128 := by have := hk 0 (by decide) 0 (by decide); omega
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.vpre42 k hk0 hsi) fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoop (N := 16) (by decide) (by decide)
    (fun i u => VG.Proof.MlKem.X86_64.S16 u.mem (VG.Proof.MlKem.X86_64.spW sP) (VG.Proof.MlKem.X86_64.layF blk F 2 zi (4 * i)) ∧ u.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (16 * i) ∧
      u.gpr .r8 = VG.Proof.MlKem.X86_64.wAddr sP (kz i) ∧ VG.Proof.MlKem.X86_64.BInv sP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, VG.Proof.MlKem.X86_64.wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ou.consts (og.consts hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : VG.Proof.MlKem.X86_64.T16 u.mem sP := (by rw [og.mem]; exact hT : T16 w.mem sP).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show VG.Proof.MlKem.X86_64.pre2 o dz ++ bf ++ [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
      .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      ([.alu .sub .rcx (.imm 1)] : List Instr) = VG.Proof.MlKem.X86_64.pre2 o dz ++ (bf ++ VG.Proof.MlKem.X86_64.post2) by simp [List.append_assoc]]
  exact WP.mono (VG.Proof.MlKem.X86_64.vstep2 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩
end

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VPack`. -/
section

/-!
# ML-KEM on x86-64: polynomials between `u32`s and words

`vpack` stores the 256 `u32`s of a reduced polynomial as words (`vpack_ok`),
and `vunpack` the words back as `u32`s (`vunpack_ok`), eight at a time.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Doublewords and words -/

theorem satSignedWord_small {x : BitVec 32} (h : x.toNat < 32768) : satSignedWord x = x.setWidth 16 := by
  have e : x.toInt = x.toNat := by rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by bdd_omega)]
  rw [satSignedWord, ite_eq_right (by bdd_omega), ite_eq_right (by bdd_omega)]

theorem word_packssdw_small (a b : BitVec 128) {e : Nat} (he : e < 8)
    (ha : ∀ j < 4, (dword a j).toNat < 32768) (hb : ∀ j < 4, (dword b j).toNat < 32768) :
    (word (XBinOp.eval .packssdw a b) e).toNat = if e < 4 then (dword a e).toNat else (dword b (e - 4)).toNat := by
  rw [word_packssdw _ _ he]
  split
  · rw [VG.Proof.MlKem.X86_64.satSignedWord_small (ha e (by bdd_omega)), BitVec.toNat_setWidth]; have := ha e (by bdd_omega); omega
  · rw [VG.Proof.MlKem.X86_64.satSignedWord_small (hb (e - 4) (by bdd_omega)), BitVec.toNat_setWidth]; have := hb (e - 4) (by bdd_omega); omega

theorem dword_eq_words (x : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword x j).toNat = (word x (2 * j)).toNat + 65536 * (word x (2 * j + 1)).toNat := by
  have h0 := word_dword x hj 0 (by decide)
  have h1 := word_dword x hj 1 (by decide)
  rw [Nat.mul_zero, Nat.add_zero] at h0
  rw [h0, h1, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have := (dword x j).isLt
  omega

/-- The `u32`s that `punpcklwd` with zeros leaves: the low words, zero-extended. -/
theorem dword_punpcklwd0 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XBinOp.eval .punpcklwd a 0) j).toNat = (word a j).toNat := by
  rw [VG.Proof.MlKem.X86_64.dword_eq_words _ hj, word_punpcklwd _ _ (by bdd_omega), word_punpcklwd _ _ (by bdd_omega),
    ite_eq_left (by bdd_omega), ite_eq_right (by bdd_omega), show 2 * j / 2 = j by bdd_omega,
    show (2 * j + 1) / 2 = j by bdd_omega]
  have : (word (0 : BitVec 128) j).toNat = 0 := by
    rw [word, BitVec.extractLsb'_toNat]; simp
  omega

/-- The `u32`s that `punpckhwd` with zeros leaves: the high words, zero-extended. -/
theorem dword_punpckhwd0 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XBinOp.eval .punpckhwd a 0) j).toNat = (word a (4 + j)).toNat := by
  rw [VG.Proof.MlKem.X86_64.dword_eq_words _ hj, word_punpckhwd _ _ (by bdd_omega), word_punpckhwd _ _ (by bdd_omega),
    ite_eq_left (by bdd_omega), ite_eq_right (by bdd_omega), show 4 + 2 * j / 2 = 4 + j by bdd_omega,
    show 4 + (2 * j + 1) / 2 = 4 + j by bdd_omega]
  have : (word (0 : BitVec 128) (4 + j)).toNat = 0 := by
    rw [word, BitVec.extractLsb'_toNat]; simp
  omega

/-! ## Packing -/

theorem coeffAddr_off (p : Addr) (j k : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4 * k) = coeffAddr p (j + k) := by
  rw [coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

/-- The eight coefficients of a reduced polynomial at `coeffAddr p j`, as the
words `packssdw` makes of them. -/
theorem lanes_pack {m : Mem} {p : Addr} {F : Poly} (hF : PolyIs m p F) {j : Nat} (hj : j + 8 ≤ 256) :
    VG.Proof.MlKem.X86_64.Lanes (XBinOp.eval .packssdw (m.readW (coeffAddr p j) 128) (m.readW (coeffAddr p (j + 4)) 128))
      (fun e => F[j + e]!) := fun e he => by
  have hc : ∀ k, k < 256 → (coeffAt m p k).toNat = (F[k]!).val := fun k hk =>
    polyIs_toNat hF (by rw [n_eq]; exact hk)
  rw [VG.Proof.MlKem.X86_64.word_packssdw_small _ _ he (fun k hk => by
      rw [dword_readW _ _ hk, VG.Proof.MlKem.X86_64.coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; have := val_lt F[j + k]!; omega)
    (fun k hk => by
      rw [dword_readW _ _ hk, VG.Proof.MlKem.X86_64.coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; have := val_lt F[j + 4 + k]!; omega)]
  split
  · rw [dword_readW _ _ (by bdd_omega), VG.Proof.MlKem.X86_64.coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]
  · rw [dword_readW _ _ (by bdd_omega), VG.Proof.MlKem.X86_64.coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega),
      show j + 4 + (e - 4) = j + e by bdd_omega]

/-- The words of the polynomial below `t`. -/
def S16p (m : Mem) (p : Addr) (F : Poly) (t : Nat) : Prop := ∀ i < t, (VG.Proof.MlKem.X86_64.wordAt m p i).toNat = (F[i]!).val

theorem polyR_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) : (pR p).Contains (coeffAddr p j) 16 :=
  Offset.contains_base p (by bdd_omega) (by bdd_omega)

theorem vpack_ok {fP sP : Addr} {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hF : PolyIs s.mem fP F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.spW sP) (hrf : pR fP ∈ s.rd ++ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vpack s fun s' => VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) F ∧ Frame [VG.Proof.MlKem.X86_64.sR (VG.Proof.MlKem.X86_64.spW sP)] s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.VConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (VG.Proof.MlKem.X86_64.sR (VG.Proof.MlKem.X86_64.spW sP)) (pR sP) := Offset.sub_base sP (by bdd_omega)
  refine WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u w => VG.Proof.MlKem.X86_64.S16p w.mem (VG.Proof.MlKem.X86_64.spW sP) F (8 * u) ∧ w.gpr .r9 = coeffAddr fP (8 * u) ∧
      w.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (8 * u) ∧ Frame [VG.Proof.MlKem.X86_64.sR (VG.Proof.MlKem.X86_64.spW sP)] s.mem w.mem ∧ VG.Proof.MlKem.X86_64.VConsts w ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hcx => ⟨fun _ h => absurd h (by bdd_omega), by rw [o.keep.gpr (by decide), h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), hdx, VG.Proof.MlKem.X86_64.wAddr]; simp, by rw [o.mem]; exact Frame.refl _ _, o.consts hc,
      o.keep.mono (by simp), o.mxcsr⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', hk', hx'⟩ => ⟨hP, hf, hc', hk', hx'⟩
  have hF' : PolyIs w.mem fP F := polyIs_frame hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.sub_right hsub) hF
  have hrf' : pR fP ∈ w.rd ++ w.wr := by rw [hk'.2.1, hk'.2.2]; exact hrf
  have hw' : pR sP ∈ w.wr := by rw [hk'.2.2]; exact hw
  have r0 : InRegions (w.rd ++ w.wr) (coeffAddr fP (8 * u)) 16 := ⟨_, hrf', VG.Proof.MlKem.X86_64.polyR_contains fP (by bdd_omega)⟩
  have r1 : InRegions (w.rd ++ w.wr) (coeffAddr fP (8 * u + 4)) 16 := ⟨_, hrf', VG.Proof.MlKem.X86_64.polyR_contains fP (by bdd_omega)⟩
  have w0 : InRegions w.wr (VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (8 * u)) 16 := VG.Proof.MlKem.X86_64.sp_in hw' (by bdd_omega)
  have a1 : coeffAddr fP (8 * u) + BitVec.ofNat 64 16 = coeffAddr fP (8 * u + 4) := VG.Proof.MlKem.X86_64.coeffAddr_off _ _ 4
  vrunm [h9', hdx', r0, r1, w0, a1, sx32]
  have lp := VG.Proof.MlKem.X86_64.lanes_pack hF' (j := 8 * u) (by bdd_omega)
  refine ⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, VG.Proof.MlKem.X86_64.coeffAddr_off,
      Nat.mul_succ],
    by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, VG.Proof.MlKem.X86_64.wAddr_add, Nat.mul_succ], ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.MlKem.X86_64.wordAt_write128 _ _ (by bdd_omega) _ (by bdd_omega)]
    split
    · rw [lp _ (by bdd_omega)]; dsimp only; rw [show 8 * u + (j - 8 * u) = j by bdd_omega]
    · exact hP j (by bdd_omega)
  · exact hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.sR_contains _ (by bdd_omega)))
  · constructor <;> simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, VG.Proof.MlKem.X86_64.xmm_setXmm, reduceCtorEq, ite_false] <;>
      [exact hc'.q; exact hc'.qinv]
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    exact hk'.gpr (by simp [hr])
  · exact hx'

/-! ## Unpacking -/

theorem S16.frame {m m' : Mem} {p : Addr} {F : Poly} (h : VG.Proof.MlKem.X86_64.S16 m p F) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.X86_64.sR p).Disjoint r) : VG.Proof.MlKem.X86_64.S16 m' p F := fun i hi => by
  rw [VG.Proof.MlKem.X86_64.wordAt, hf.readW (Offset.contains_base p (by bdd_omega) (by bdd_omega)) hd (by decide)]; exact h i hi

/-- Coefficient `i` after storing `x` at coefficient `j`. -/
theorem coeffAt_write128 (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i = if j ≤ i ∧ i < j + 4 then dword x (i - j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [VG.Proof.MlKem.X86_64.coeffAddr_off, show j + (i - j) = i by bdd_omega]]
    exact readW_writeW128 _ _ _ (by bdd_omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)) (by decide)

/-- The coefficients below `t`. -/
def PolyP (m : Mem) (p : Addr) (F : Poly) (t : Nat) : Prop := ∀ i < t, (coeffAt m p i).toNat = (F[i]!).val

theorem vunpack_ok {fP sP : Addr} {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.spW sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vunpack s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.VConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (VG.Proof.MlKem.X86_64.sR (VG.Proof.MlKem.X86_64.spW sP)) (pR sP) := Offset.sub_base sP (by bdd_omega)
  refine WP.seq (WP.mono (Q := fun (w : State) => w.xmm .xmm4 = 0 ∧ VG.Proof.MlKem.X86_64.XOnly [.xmm4] s w)
    (by vrunm; exact ⟨by simp only [XBinOp.eval, BitVec.xor_self]; rfl, by xonly⟩) fun w0 ⟨hz, o0⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u w => VG.Proof.MlKem.X86_64.PolyP w.mem fP F (8 * u) ∧ w.gpr .r9 = coeffAddr fP (8 * u) ∧
      w.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (8 * u) ∧ Frame [pR fP] s.mem w.mem ∧ VG.Proof.MlKem.X86_64.VConsts w ∧ w.xmm .xmm4 = 0 ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hcx => ⟨fun _ h => absurd h (by bdd_omega),
      by rw [o.keep.gpr (by decide), o0.gpr, h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), o0.gpr, hdx, VG.Proof.MlKem.X86_64.wAddr]; simp, by rw [o.mem, o0.mem]; exact Frame.refl _ _,
      o.consts (o0.consts hc (by decide) (by decide)), by rw [o.xmm, hz],
      Keep.trans (⟨fun r _ => by rw [o0.gpr], o0.rd, o0.wr⟩ : Keep [] s w0) (o.keep) |>.mono (by simp),
      by rw [o.mxcsr, o0.mxcsr]⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hz', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', _, hk', hx'⟩ => ⟨polyIs_of_toNat fun i hi => hP i (by rw [n_eq] at hi; omega),
      hf, hc', hk', hx'⟩
  have hS' : VG.Proof.MlKem.X86_64.S16 w.mem (VG.Proof.MlKem.X86_64.spW sP) F := hS.frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_right hsub).symm
  have hwf' : pR fP ∈ w.wr := by rw [hk'.2.2]; exact hwf
  have r0 : InRegions (w.rd ++ w.wr) (VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (8 * u)) 16 :=
    VG.Proof.MlKem.X86_64.sp_in (List.mem_append_right _ (by rw [hk'.2.2]; exact hw)) (by bdd_omega)
  have w0 : InRegions w.wr (coeffAddr fP (8 * u)) 16 := ⟨_, hwf', VG.Proof.MlKem.X86_64.polyR_contains fP (by bdd_omega)⟩
  have w1 : InRegions w.wr (coeffAddr fP (8 * u + 4)) 16 := ⟨_, hwf', VG.Proof.MlKem.X86_64.polyR_contains fP (by bdd_omega)⟩
  have a1 : coeffAddr fP (8 * u) + BitVec.ofNat 64 16 = coeffAddr fP (8 * u + 4) := VG.Proof.MlKem.X86_64.coeffAddr_off _ _ 4
  have ll := VG.Proof.MlKem.X86_64.lanes_load hS' (j := 8 * u) (by bdd_omega)
  vrunm [h9', hdx', r0, w0, w1, a1, sx32, hz']
  refine ⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, VG.Proof.MlKem.X86_64.coeffAddr_off,
      Nat.mul_succ],
    by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, VG.Proof.MlKem.X86_64.wAddr_add, Nat.mul_succ], ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.MlKem.X86_64.coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega), VG.Proof.MlKem.X86_64.coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega)]
    split
    · rw [VG.Proof.MlKem.X86_64.dword_punpckhwd0 _ (by bdd_omega), word_movdqa, ll _ (by bdd_omega)]; dsimp only
      rw [show 8 * u + (4 + (j - (8 * u + 4))) = j by bdd_omega]
    · split
      · rw [VG.Proof.MlKem.X86_64.dword_punpcklwd0 _ (by bdd_omega), ll _ (by bdd_omega)]; dsimp only
        rw [show 8 * u + (j - 8 * u) = j by bdd_omega]
      · exact hP j (by bdd_omega)
  · exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.polyR_contains fP (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.polyR_contains fP (by bdd_omega)))
  · constructor <;> simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, VG.Proof.MlKem.X86_64.xmm_setXmm, reduceCtorEq, ite_false] <;>
      [exact hc'.q; exact hc'.qinv]
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    exact hk'.gpr (by simp [hr])
  · exact hx'

/-! ## The multiplication by 3303 -/

/-- `vmont` then `vcadd`: each word of `d` times the constant `c`, reduced, with
`c · 2¹⁶ mod q` in the words of `z`. -/
theorem vmulc_ok {d z t : XReg} (h2 : t ≠ d) (h3 : z ≠ t) (h4 : XReg.xmm14 ≠ d) (h5 : XReg.xmm15 ≠ d)
    (h6 : XReg.xmm14 ≠ t) (h7 : XReg.xmm15 ≠ t) {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) {x : Nat → Zq} {c : Zq} (hx : VG.Proof.MlKem.X86_64.Lanes (s.xmm d) x)
    (hz : VG.Proof.MlKem.X86_64.ZLanes (s.xmm z) fun _ => c) :
    WP isa (.block (vmont d z t ++ vcadd d t)) s fun s' => VG.Proof.MlKem.X86_64.Lanes (s'.xmm d) (fun i => c * x i) ∧
      VG.Proof.MlKem.X86_64.XOnly [d, t] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vmont_ok h2 h3 h5 h6 h7 hc) fun s1 ⟨l1, o1⟩ =>
    WP.mono (VG.Proof.MlKem.X86_64.vcadd_ok h2 h7 (o1.consts hc
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h6⟩)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h5, h7⟩)))
      fun s2 ⟨l2, o2⟩ => ⟨fun i hi => ?_, (o1.trans o2).mono (by simp)⟩
  · rw [l2 i hi]; dsimp only; rw [l1 i hi]; dsimp only
    have hxl := val_lt (x i)
    have hxi := W.toInt_of_lt (a := word (s.xmm d) i) (by rw [hx i hi]; exact hxl)
    rw [hx i hi] at hxi
    have r := W.mulZ_spec (b := word (s.xmm d) i) (y := x i) (ζ := c) (by bdd_omega) (by bdd_omega)
      (by rw [hxi, Int.sub_self]; rfl) (hz i hi)
    have n := W.toNat_of_toInt (a := W.caddW (W.montW (word (s.xmm d) i) (word (s.xmm z) i)))
      (by rw [r]; exact Int.natCast_nonneg _)
    rw [r] at n
    exact Int.ofNat.inj n

/-- `3303 · 2¹⁶ mod q = 512` in every word, as `vscale` makes it. -/
theorem zlanes_512 : VG.Proof.MlKem.X86_64.ZLanes (shufDwords ((0 : BitVec 64) ++ BitVec.setWidth 64 (0x02000200 : BitVec 32)) 0)
    fun _ => (3303 : Zq) := fun i hi => by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem vscale_ok {sP : Addr} {F : Poly} {s : State} (hc : VG.Proof.MlKem.X86_64.VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : VG.Proof.MlKem.X86_64.S16 s.mem (VG.Proof.MlKem.X86_64.spW sP) F) (hw : pR sP ∈ s.wr) :
    WP isa vscale s fun s' => VG.Proof.MlKem.X86_64.S16 s'.mem (VG.Proof.MlKem.X86_64.spW sP) (F.map (· * 3303)) ∧ VG.Proof.MlKem.X86_64.BInv sP s s' := by
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = VG.Proof.MlKem.X86_64.spW sP ∧
      VG.Proof.MlKem.X86_64.ZLanes (w.xmm .xmm13) (fun _ => (3303 : Zq)) ∧ VG.Proof.MlKem.X86_64.GKeep [.rdx, .rax] s w ∧ VG.Proof.MlKem.X86_64.VConsts w)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), hsi]
      refine ⟨VG.Proof.MlKem.X86_64.zlanes_512, ⟨⟨fun r hr => ?_, rfl, rfl⟩, rfl, rfl⟩, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      · constructor <;> simp only [VG.Proof.MlKem.X86_64.xmm_setXmm, RegUpd.xmm_setReg, reduceCtorEq, ite_false] <;>
          [exact hc.q; exact hc.qinv])
    fun w ⟨hdx, hz, og, hcw⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u v => (∀ j < 256, (VG.Proof.MlKem.X86_64.wordAt v.mem (VG.Proof.MlKem.X86_64.spW sP) j).toNat = (if j < 8 * u then F[j]! * 3303 else F[j]!).val) ∧
      v.gpr .rdx = VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (8 * u) ∧ v.xmm .xmm13 = w.xmm .xmm13 ∧ VG.Proof.MlKem.X86_64.BInv sP s v)
    (fun v o hcx => ⟨fun j hj => by rw [ite_eq_right (by bdd_omega), o.mem, og.mem]; exact hS j hj,
      by rw [o.keep.gpr (by decide), hdx, VG.Proof.MlKem.X86_64.wAddr]; simp, by rw [o.xmm],
      ⟨(og.keep.trans o.keep).mono (by simp), by rw [o.mem, og.mem]; exact Frame.refl _ _, o.consts hcw,
        by rw [o.mxcsr, og.mxcsr]⟩⟩)
    (fun u hu v ⟨hP, hdx', hz', hb⟩ => ?_))
    fun v ⟨hP, _, _, hb⟩ => ⟨fun j hj => by rw [hP j hj, ite_eq_left (by bdd_omega), map_mul_get _ (by rw [n_eq]; exact hj)],
      hb⟩
  have hw' : pR sP ∈ v.wr := by rw [hb.keep.2.2]; exact hw
  have r0 := VG.Proof.MlKem.X86_64.sp_in (List.mem_append_right v.rd hw') (j := 8 * u) (by bdd_omega)
  have w0 := VG.Proof.MlKem.X86_64.sp_in hw' (j := 8 * u) (by bdd_omega)
  rw [show [Instr.movdquLoad .xmm3 (VG.Impl.MlKem.X86_64.at_ .rdx 0)] ++ vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2 ++
      ([.movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16)] : List Instr) ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [Instr.movdquLoad .xmm3 (VG.Impl.MlKem.X86_64.at_ .rdx 0)] ++ ((vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2) ++
        ([.movdquStore (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr)) by
      simp [List.append_assoc], WP.block_append_iff]
  vrunm [hdx', r0]
  rw [WP.block_append_iff]
  have lx : VG.Proof.MlKem.X86_64.Lanes ((v.setXmm .xmm3 (v.mem.readW (VG.Proof.MlKem.X86_64.wAddr (VG.Proof.MlKem.X86_64.spW sP) (8 * u)) 128)).xmm .xmm3)
      (fun e => F[8 * u + e]!) := fun e he => by
    rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifp rfl, word_readW _ _ he, VG.Proof.MlKem.X86_64.wAddr_add, ← VG.Proof.MlKem.X86_64.wordAt, hP _ (by bdd_omega), ite_eq_right (by bdd_omega)]
  refine WP.mono (VG.Proof.MlKem.X86_64.vmulc_ok (d := .xmm3) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hb.consts.setXmm (by decide) (by decide) _) lx (c := 3303)
    (by rw [VG.Proof.MlKem.X86_64.xmm_setXmm, ifn (by decide), hz']; exact hz)) fun v2 ⟨l2, o2⟩ => ?_
  have g2 : v2.gpr .rdx = v.gpr .rdx := by rw [o2.gpr]; rfl
  have e2 : v2.rd = v.rd ∧ v2.wr = v.wr := ⟨o2.rd, o2.wr⟩
  have m2 : v2.mem = v.mem := o2.mem
  vrunm [g2, e2.1, e2.2, m2, hdx', w0]
  have rc2 : v2.gpr .rcx = v.gpr .rcx := by rw [o2.gpr]; rfl
  refine ⟨⟨fun j hj => ?_, by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, VG.Proof.MlKem.X86_64.wAddr_add, Nat.mul_succ],
    by rw [o2.xmm _ (by decide), VG.Proof.MlKem.X86_64.xmm_setXmm, ifn (by decide), hz'], ?_⟩, by rw [rc2], by rw [rc2]⟩
  · rw [VG.Proof.MlKem.X86_64.wordAt_write128 _ _ (by bdd_omega) _ hj]
    split
    · rw [l2 _ (by bdd_omega)]; dsimp only
      rw [ite_eq_left (by bdd_omega), show 8 * u + (j - 8 * u) = j by bdd_omega, Fin.mul_comm]
    · rw [hP j hj]
      by_cases h : j < 8 * u
      · rw [ite_eq_left h, ite_eq_left (by bdd_omega)]
      · rw [ite_eq_right h, ite_eq_right (by bdd_omega)]
  · refine hb.trans ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩,
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.sR_contains _ (by bdd_omega)), ?_,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; exact o2.mxcsr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr]; rfl
    · exact ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact (o2.consts
          (hb.consts.setXmm (by decide) (by decide) _) (by decide) (by decide)).q,
        by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact (o2.consts
          (hb.consts.setXmm (by decide) (by decide) _) (by decide) (by decide)).qinv⟩

/-! ## The table of zetas -/

theorem readW_writeW64_16 (m : Mem) (a : Addr) (v : BitVec 64) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (2 * j)) 16 = v.extractLsb' (16 * j) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by bdd_omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (2 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)]
  simp only [show 2 * j + i / 8 < 64 / 8 by bdd_omega, ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by bdd_omega), decide_eq_true (by bdd_omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by bdd_omega)

/-- Four words packed into a quadword, as `wordTab` makes its immediates. -/
theorem quad_word {t0 t1 t2 t3 : Nat} (h0 : t0 < 65536) (h1 : t1 < 65536) (h2 : t2 < 65536) (h3 : t3 < 65536)
    {e : Nat} (he : e < 4) :
    ((BitVec.ofNat 64 (t0 + 2 ^ 16 * t1 + 2 ^ 32 * t2 + 2 ^ 48 * t3)).extractLsb' (16 * e) 16).toNat =
      [t0, t1, t2, t3][e]! := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rcases (by bdd_omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceMul, List.getElem!_cons_zero, List.getElem!_cons_succ] <;> omega

theorem zmTab_lt (k : Nat) : zmTab k < 65536 := by
  have : zmTab k < 3329 := Nat.mod_lt _ (by decide)
  omega

theorem zmTab_eq (k : Nat) : zmTab k = (zeta k).val * 65536 % 3329 := by
  rw [zmTab, zeta, val_pow, Nat.mod_mul_mod]; rfl

/-- A table of 128 words `t k`, stored at `sP` (in `r`), through `r9`. -/
theorem wordTab_gen (t : Nat → Nat) (ht : ∀ k, t k < 65536) {r : Reg} (hr : r ≠ .r9) {sP : Addr} {s : State}
    (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (wordTab t 128 r 0)) s fun s' => (∀ k < 128, (VG.Proof.MlKem.X86_64.wordAt s'.mem sP k).toNat = t k) ∧
      Frame [⟨sP, 256⟩] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr ∧ s'.xmm = s.xmm := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 32) (fun i w =>
      (∀ k < 4 * i, (VG.Proof.MlKem.X86_64.wordAt w.mem sP k).toNat = t k) ∧ Frame [⟨sP, 256⟩] s.mem w.mem ∧
        Keep [.r9] s w ∧ w.mxcsr = s.mxcsr ∧ w.xmm = s.xmm)
    (fun i w hi ⟨hT, hf, hk, hm, hx⟩ => ?_) 32 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by bdd_omega), Frame.refl _ _, Keep.refl _ _, rfl, rfl⟩)
    fun w ⟨hT, hf, hk, hm, hx⟩ => ⟨fun k hk' => hT k (by bdd_omega), hf, hk, hm, hx⟩
  have hsi' : w.gpr r = sP := by
    rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have w0 : InRegions w.wr (sP + BitVec.ofNat 64 (0 + 8 * i)) 8 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by bdd_omega) (by bdd_omega)⟩
  have hV : ∀ e < 4, ((BitVec.ofNat 64 (t (4 * i) + 2 ^ 16 * t (4 * i + 1) +
      2 ^ 32 * t (4 * i + 2) + 2 ^ 48 * t (4 * i + 3))).extractLsb' (16 * e) 16).toNat =
        t (4 * i + e) := fun e he => by
    rw [VG.Proof.MlKem.X86_64.quad_word (ht _) (ht _) (ht _) (ht _) he]
    rcases (by bdd_omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl
  vrunm [hsi', w0, hr]
  generalize BitVec.ofNat 64 (t (4 * i) + 2 ^ 16 * t (4 * i + 1) +
      2 ^ 32 * t (4 * i + 2) + 2 ^ 48 * t (4 * i + 3)) = V at hV ⊢
  refine ⟨fun k hk' => ?_, hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base sP (by bdd_omega) (by bdd_omega)),
    ⟨fun r hr => ?_, hk.2.1, hk.2.2⟩, hm, hx⟩
  · by_cases h : 4 * i ≤ k
    · rw [VG.Proof.MlKem.X86_64.wordAt, VG.Proof.MlKem.X86_64.wAddr, show sP + BitVec.ofNat 64 (2 * k) =
          sP + BitVec.ofNat 64 (0 + 8 * i) + BitVec.ofNat 64 (2 * (k - 4 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by bdd_omega)),
        VG.Proof.MlKem.X86_64.readW_writeW64_16 _ _ _ (by bdd_omega), hV _ (by bdd_omega), show 4 * i + (k - 4 * i) = k by bdd_omega]
    · rw [VG.Proof.MlKem.X86_64.wordAt, Mem.readW_writeW_sep (Offset.sep sP (by bdd_omega) (by bdd_omega) (by bdd_omega)) (by decide)]
      exact hT k (by bdd_omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
    exact hk.1 r (by simp [hr])

/-- The table of zetas, stored at `scratch` (`rsi`), through `r9`. -/
theorem wordTab_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (wordTab zmTab 128 .rsi 0)) s fun s' => VG.Proof.MlKem.X86_64.T16 s'.mem sP ∧
      Frame [⟨sP, 256⟩] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr ∧ s'.xmm = s.xmm :=
  WP.mono (VG.Proof.MlKem.X86_64.wordTab_gen zmTab VG.Proof.MlKem.X86_64.zmTab_lt (by decide) hsi hw) fun _ ⟨hT, rest⟩ =>
    ⟨fun k hk => by rw [hT k hk, VG.Proof.MlKem.X86_64.zmTab_eq], rest⟩

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.AddSub`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_add` and `vg_mlkem_sub`

A doubleword of the result is `condSub` of the sum (`add_lane`, `sub_lane`);
the loop stores four of them at a time to `f` (`AddSub.Inv`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## One doubleword -/

/-- `d + q` if `d` is negative (as a signed doubleword), else `d`: `dcadd` on one doubleword. -/
def cadd32 (d : BitVec 32) : BitVec 32 := d + (d.sshiftRight 31 &&& 3329#32)

theorem sshiftRight31 (d : BitVec 32) : d.sshiftRight 31 = if d.toNat < 2 ^ 31 then 0 else -1 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, W.toInt32]
  have := d.isLt
  split
  · rw [show (0 : BitVec 32).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega
  · rw [show (-1 : BitVec 32).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega

theorem cadd32_toNat (d : BitVec 32) :
    (VG.Proof.MlKem.X86_64.cadd32 d).toNat = if d.toNat < 2 ^ 31 then d.toNat else (d.toNat + 3329) % 2 ^ 32 := by
  rw [VG.Proof.MlKem.X86_64.cadd32, VG.Proof.MlKem.X86_64.sshiftRight31]
  split
  · rw [show (0 : BitVec 32) &&& 3329#32 = 0 by decide]; exact congrArg BitVec.toNat (BitVec.add_zero d)
  · rw [show (-1 : BitVec 32) &&& 3329#32 = 3329#32 by decide, BitVec.toNat_add]; rfl

/-- A lane of `add`. -/
theorem add_lane {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlKem.X86_64.cadd32 (a + b - 3329#32)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b - 3329#32).toNat = (a.toNat + b.toNat + 2 ^ 32 - 3329) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add]; rw [q_eq] at *; simp only [BitVec.toNat_ofNat]; omega
  rw [VG.Proof.MlKem.X86_64.cadd32_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega

/-- A lane of `sub`. -/
theorem sub_lane {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlKem.X86_64.cadd32 (a - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a - b).toNat = (a.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega
  rw [VG.Proof.MlKem.X86_64.cadd32_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega

/-! ## Four doublewords -/

theorem dword_psubd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .psubd a b) i = dword a i - dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_pand (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .pand a b) i = dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_psrad31 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrad a 31) i = (dword a i).sshiftRight 31 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval]

/-- `q` in each doubleword. -/
def qD : BitVec 128 := 0x00000D0100000D0100000D0100000D01#128

theorem dword_qD {i : Nat} (hi : i < 4) : dword VG.Proof.MlKem.X86_64.qD i = 3329#32 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

theorem addBody_ok {s : State} (hq : s.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) (h3 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block addBody) s fun s' => (∃ X, s'.mem = s.mem.writeW (s.gpr .rdi) X ∧
      ∀ j < 4, dword X j = VG.Proof.MlKem.X86_64.cadd32 (dword (s.mem.readW (s.gpr .rdi) 128) j +
        dword (s.mem.readW (s.gpr .rsi) 128) j - 3329#32)) ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD ∧ Keep [.rdi, .rsi, .rcx] s s' := by
  simp only [addBody, dcadd, dstep]
  vrunm [h1, h2, h3, eval_movdqa]
  refine ⟨⟨_, rfl, fun j hj => ?_⟩, hq, fun r hr => ?_, rfl, rfl⟩
  · simp only [dword_paddd _ _ hj, VG.Proof.MlKem.X86_64.dword_psubd _ _ hj, VG.Proof.MlKem.X86_64.dword_pand, VG.Proof.MlKem.X86_64.dword_psrad31 _ hj, hq, VG.Proof.MlKem.X86_64.dword_qD hj]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
theorem subBody_ok {s : State} (hq : s.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) (h3 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block subBody) s fun s' => (∃ X, s'.mem = s.mem.writeW (s.gpr .rdi) X ∧
      ∀ j < 4, dword X j = VG.Proof.MlKem.X86_64.cadd32 (dword (s.mem.readW (s.gpr .rdi) 128) j -
        dword (s.mem.readW (s.gpr .rsi) 128) j)) ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD ∧ Keep [.rdi, .rsi, .rcx] s s' := by
  simp only [subBody, dcadd, dstep]
  vrunm [h1, h2, h3, eval_movdqa]
  refine ⟨⟨_, rfl, fun j hj => ?_⟩, hq, fun r hr => ?_, rfl, rfl⟩
  · simp only [dword_paddd _ _ hj, VG.Proof.MlKem.X86_64.dword_psubd _ _ hj, VG.Proof.MlKem.X86_64.dword_pand, VG.Proof.MlKem.X86_64.dword_psrad31 _ hj, hq, VG.Proof.MlKem.X86_64.dword_qD hj]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

/-! ## The loop -/

namespace AddSub

/-- After `i` groups of four coefficients, each one `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (4 * i)
  rsi : s.gpr .rsi = coeffAddr (s₀.gpr .rsi) (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : s.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 4 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

/-- What a body does: store `v` of the next four coefficients. -/
def Body (v : Nat → BitVec 32) (i : Nat) (s s' : State) : Prop :=
  (∃ X, s'.mem = s.mem.writeW (s.gpr .rdi) X ∧ ∀ j < 4, dword X j = v (4 * i + j)) ∧
    s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
    s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD ∧ Keep [.rdi, .rsi, .rcx] s s'

theorem step16 (p : Addr) (i : Nat) : coeffAddr p (4 * i) + 16 = coeffAddr p (4 * (i + 1)) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, VG.Proof.MlKem.X86_64.coeffAddr_off, Nat.mul_succ]

theorem inv_step {s₀ : State} {v : Nat → BitVec 32} {i : Nat} (hi : i < 64) {s s' : State}
    (hI : VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v i s) (hb : VG.Proof.MlKem.X86_64.AddSub.Body v i s s') : VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v (i + 1) s' := by
  obtain ⟨⟨X, hm, hX⟩, hdi, hsi, -, -, hq, hk⟩ := hb
  refine ⟨by rw [hdi, hI.rdi, VG.Proof.MlKem.X86_64.AddSub.step16], by rw [hsi, hI.rsi, VG.Proof.MlKem.X86_64.AddSub.step16], hk.2.1.trans hI.rd,
    hk.2.2.trans hI.wr, hq, ?_, fun k hk' => ?_⟩
  · rw [hm, hI.rdi]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, hI.rdi, VG.Proof.MlKem.X86_64.coeffAt_write128 _ _ (by omega) _ hk', hI.coeff k hk']
    by_cases e : 4 * i ≤ k ∧ k < 4 * i + 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e), hX _ (by omega), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        show 4 * i + (k - 4 * i) = k by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
      by_cases e' : k < 4 * i
      · rw [ite_eq_left_of_eq_true _ _ (eq_true e'), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false e'), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
include hp

theorem regions {v : Nat → BitVec 32} {i : Nat} (hi : i < 64) {s : State} (hI : VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v i s) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16 ∧ InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16 ∧
      InRegions s.wr (s.gpr .rdi) 16 := by
  rw [hI.rd, hI.wr, hI.rdi, hI.rsi, hp.1, hp.2.1]
  exact ⟨⟨pR _, List.mem_append_right _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩,
    ⟨pR _, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩,
    ⟨pR _, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩⟩

/-- The coefficients a body reads. -/
theorem reads {v : Nat → BitVec 32} {i : Nat} (hi : i < 64) {s : State} (hI : VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v i s) {j : Nat}
    (hj : j < 4) :
    dword (s.mem.readW (s.gpr .rdi) 128) j = coeffAt s₀.mem (s₀.gpr .rdi) (4 * i + j) ∧
      dword (s.mem.readW (s.gpr .rsi) 128) j = coeffAt s₀.mem (s₀.gpr .rsi) (4 * i + j) := by
  refine ⟨?_, ?_⟩
  · rw [dword_readW _ _ hj, hI.rdi, VG.Proof.MlKem.X86_64.coeffAddr_off, ← coeffAt_eq, hI.coeff _ (by omega),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [dword_readW _ _ hj, hI.rsi, VG.Proof.MlKem.X86_64.coeffAddr_off, ← coeffAt_eq]
    exact coeffAt_congr (bytes_frame hI.frame (by simpa using hp.2.2.1.symm) (by decide)) (by rw [n_eq]; omega)

/-- The whole function, from its precondition. -/
theorem fn_ok {body : List Instr} {v : Nat → BitVec 32}
    (hbody : ∀ i < 64, ∀ s, VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v i s → WP isa (.block body) s (VG.Proof.MlKem.X86_64.AddSub.Body v i s))
    (hv : ∀ i < 256, (v i).toNat = ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[i]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx]
      (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne)) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i)
      (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne)) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hL : WP isa (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne)) s₀
      (VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v 64) := by
    refine WP.seq (WP.mono (Q := fun (s : State) => s.xmm .xmm15 = VG.Proof.MlKem.X86_64.qD ∧ s.gpr .rcx = BitVec.ofNat 64 64 ∧
        s.mem = s₀.mem ∧ Keep [.rax, .rcx] s₀ s) (by
          simp only [dconsts]
          vrunm
          refine ⟨fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun s ⟨hq, hcx, hm0, k0⟩ => ?_)
    refine wp_countdown (cnt := .rcx) (N := 64) (by decide) (by decide) (VG.Proof.MlKem.X86_64.AddSub.Inv s₀ v)
      (fun i hi s hI _ => WP.mono (hbody i hi s hI) fun s' hb => ⟨VG.Proof.MlKem.X86_64.AddSub.inv_step hi hI hb, hb.2.2.2.1, hb.2.2.2.2.1⟩)
      (fun _ h => h) ⟨?_, ?_, k0.2.1, k0.2.2, hq, by rw [hm0]; exact Frame.refl _ _, fun k _ => ?_⟩ hcx
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
    · rw [hm0]; exact (ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_zero _))).symm
  obtain ⟨tr, s', he, hI, hk⟩ := WP.keep _ hL hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hI.frame ?_),
    polyIs_of_toNat fun i hi => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hi
    rw [hI.coeff i hi, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; exact hv i hi

end

end AddSub

/-! ## The functions -/

theorem add_correct (s : State) (hs : (accK Spec.MlKem.add).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.add s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.add).post s s' :=
  AddSub.fn_ok hs (v := fun i => VG.Proof.MlKem.X86_64.cadd32 (coeffAt s.mem (s.gpr .rdi) i + coeffAt s.mem (s.gpr .rsi) i - 3329#32))
    (fun i hi s' hI => by
      obtain ⟨h1, h2, h3⟩ := AddSub.regions hs hi hI
      refine WP.mono (VG.Proof.MlKem.X86_64.addBody_ok hI.q h1 h2 h3) fun s'' ⟨⟨X, hm, hX⟩, rest⟩ => ⟨⟨X, hm, fun j hj => ?_⟩, rest⟩
      obtain ⟨e1, e2⟩ := AddSub.reads hs hi hI hj
      rw [hX j hj, e1, e2])
    (fun i hi => by
      rw [VG.Proof.MlKem.X86_64.add_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        add_get _ _ (by rw [n_eq]; exact hi), val_add,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide) (by decide)

theorem sub_correct (s : State) (hs : (accK Spec.MlKem.sub).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.sub s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.sub).post s s' :=
  AddSub.fn_ok hs (v := fun i => VG.Proof.MlKem.X86_64.cadd32 (coeffAt s.mem (s.gpr .rdi) i - coeffAt s.mem (s.gpr .rsi) i))
    (fun i hi s' hI => by
      obtain ⟨h1, h2, h3⟩ := AddSub.regions hs hi hI
      refine WP.mono (VG.Proof.MlKem.X86_64.subBody_ok hI.q h1 h2 h3) fun s'' ⟨⟨X, hm, hX⟩, rest⟩ => ⟨⟨X, hm, fun j hj => ?_⟩, rest⟩
      obtain ⟨e1, e2⟩ := AddSub.reads hs hi hI hj
      rw [hX j hj, e1, e2])
    (fun i hi => by
      rw [VG.Proof.MlKem.X86_64.sub_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        sub_get _ _ (by rw [n_eq]; exact hi), val_sub,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide) (by decide)

/-- The pointers and `rsp` are public. -/
def accτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (accK t).pre s₁) (_ : (accK t).pre s₂)
    (hp : (accK t).pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.MlKem.X86_64.accτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem add_ct : ConstantTime isa (accK Spec.MlKem.add).pre (accK Spec.MlKem.add).pub Impl.MlKem.X86_64.add :=
  VG.Taint.constantTime (A := taint) VG.Proof.MlKem.X86_64.accτ VG.Proof.MlKem.X86_64.acc_agree (by taint_decide)

theorem sub_ct : ConstantTime isa (accK Spec.MlKem.sub).pre (accK Spec.MlKem.sub).pub Impl.MlKem.X86_64.sub :=
  VG.Taint.constantTime (A := taint) VG.Proof.MlKem.X86_64.accτ VG.Proof.MlKem.X86_64.acc_agree (by taint_decide)

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
    Verified X86_64.target Impl.MlKem.X86_64.add (Spec.MlKem.addContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.add_correct VG.Proof.MlKem.X86_64.add_ct (by
    mlkem_implies [Spec.MlKem.addContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using VG.Proof.MlKem.X86_64.accSat)

theorem sub_verified :
    Verified X86_64.target Impl.MlKem.X86_64.sub (Spec.MlKem.subContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.sub_correct VG.Proof.MlKem.X86_64.sub_ct (by
    mlkem_implies [Spec.MlKem.subContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using VG.Proof.MlKem.X86_64.accSat)

end VG.Proof.MlKem.X86_64

end
