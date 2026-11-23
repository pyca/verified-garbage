module

import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.TCB.X86.Sse
public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.Framework.Omega
import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ML-KEM on x86 (32-bit): arithmetic modulo `q` in 16-bit words

What `wmont`, `wcadd` and `wcsub` (`Impl/MlKem/X86/Vec.lean`) compute in
each word (`montW`, `caddW`, `csubW`), on the words' signed values
(`BitVec.toInt`):

* `montW_spec`: `montW d z` is in `(-q, q)` and congruent to
  `d · z · 2⁻¹⁶` modulo `q`, if `|d · z| < q · 2¹⁵`;
* `caddW_spec`, `csubW_spec`: the value modulo `q`, in `[0, q)`, of a word in
  `(-q, q)` or `[0, 2q)`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.W

open VG VG.X86 VG.Proof.MlKem

/-- `q` as a word. -/
def qW : BitVec 16 := 3329

/-- `q⁻¹ mod 2¹⁶` as a word. -/
def qinvW : BitVec 16 := 62209

/-- The word `vmont` leaves of the words `d` and `z`. -/
def montW (d z : BitVec 16) : BitVec 16 :=
  (mulWordsSigned d z).extractLsb' 16 16 -
    (mulWordsSigned ((mulWordsSigned ((mulWordsSigned d z).extractLsb' 0 16) qinvW).extractLsb' 0 16)
      qW).extractLsb' 16 16

/-- The word `vcadd` leaves of `d`. -/
def caddW (d : BitVec 16) : BitVec 16 := d + ((d.sshiftRight (min 15 16)) &&& qW)

/-- The word `vcsub` leaves of `d`. -/
def csubW (d : BitVec 16) : BitVec 16 := caddW (d - qW)

/-! ## Words as integers -/

theorem toInt16 (x : BitVec 16) :
    x.toInt = if x.toNat < 32768 then (x.toNat : Int) else (x.toNat : Int) - 65536 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega_arith

theorem toInt32 (x : BitVec 32) :
    x.toInt = if x.toNat < 2147483648 then (x.toNat : Int) else (x.toNat : Int) - 4294967296 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega_arith

theorem toInt16_bounds (x : BitVec 16) : -32768 ≤ x.toInt ∧ x.toInt < 32768 := by
  rw [toInt16]; have := x.isLt; split <;> omega_arith

/-- The product of two words is at most `2³⁰` in magnitude. -/
theorem mul_bounds (a b : BitVec 16) : -(2 ^ 30 : Int) ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 2 ^ 30 := by
  have ha := toInt16_bounds a
  have hb := toInt16_bounds b
  have hn : (a.toInt * b.toInt).natAbs ≤ 32768 * 32768 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have h1 := Int.le_natAbs (a := a.toInt * b.toInt)
  have h2 := Int.le_natAbs (a := -(a.toInt * b.toInt))
  rw [Int.natAbs_neg] at h2
  omega_arith

theorem toInt_mulWordsSigned (a b : BitVec 16) : (mulWordsSigned a b).toInt = a.toInt * b.toInt := by
  rw [mulWordsSigned, BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by decide),
    BitVec.toInt_signExtend_of_le (by decide)]
  have := mul_bounds a b
  apply Int.bmod_eq_of_le
  · rw [show (((2 ^ 32 : Nat) : Int) / 2) = 2147483648 from rfl]; omega_arith
  · rw [show ((((2 ^ 32 : Nat) : Int) + 1) / 2) = 2147483648 from rfl]; omega_arith

/-- The high word of a doubleword: its value divided by `2¹⁶`, rounded down. -/
theorem toInt_hi (x : BitVec 32) : (x.extractLsb' 16 16).toInt = x.toInt / 65536 := by
  rw [toInt16, toInt32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  simp only [Nat.reducePow]
  split <;> split <;> omega_arith

/-- The low word of a doubleword: its value modulo `2¹⁶`. -/
theorem toInt_lo (x : BitVec 32) : ((x.extractLsb' 0 16).toInt - x.toInt) % 65536 = 0 := by
  rw [toInt16, toInt32, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have := x.isLt
  simp only [Nat.reducePow]
  split <;> split <;> omega_arith

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
    -3329 < (montW d z).toInt ∧ (montW d z).toInt < 3329 ∧
      ((montW d z).toInt * 65536 - d.toInt * z.toInt) % 3329 = 0 := by
  generalize hP : d.toInt * z.toInt = P at h1 h2
  have eP : (mulWordsSigned d z).toInt = P := by rw [toInt_mulWordsSigned, hP]
  generalize hL : (mulWordsSigned d z).extractLsb' 0 16 = L
  have hL' := toInt_lo (mulWordsSigned d z)
  rw [hL, eP] at hL'
  have bL := toInt16_bounds L
  generalize hT : (mulWordsSigned L qinvW).extractLsb' 0 16 = T
  have hT' := toInt_lo (mulWordsSigned L qinvW)
  rw [hT, toInt_mulWordsSigned, qinvW_toInt] at hT'
  have bT := toInt16_bounds T
  have hH := toInt_hi (mulWordsSigned d z)
  rw [eP] at hH
  have hM := toInt_hi (mulWordsSigned T qW)
  rw [toInt_mulWordsSigned, qW_toInt] at hM
  have e : montW d z = (mulWordsSigned d z).extractLsb' 16 16 - (mulWordsSigned T qW).extractLsb' 16 16 := by
    rw [montW, hL, hT]
  have hc : (P - T.toInt * 3329) % 65536 = 0 := by omega_arith
  have hd : P / 65536 - T.toInt * 3329 / 65536 = (P - T.toInt * 3329) / 65536 := by omega_arith
  rw [e, toInt_sub16 (by omega_arith) (by omega_arith), hH, hM, hd]
  omega_arith

/-! ## Conditional additions of `q` -/

theorem sshiftRight15 (d : BitVec 16) :
    d.sshiftRight (min 15 16) = if d.toInt < 0 then -1 else 0 := by
  rw [show min 15 16 = 15 from rfl]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight]
  have := toInt16_bounds d
  split
  · rw [show (-1 : BitVec 16).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega_arith
  · rw [show (0 : BitVec 16).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega_arith

/-- `caddW d` is the value of `d ∈ [-q, q)` modulo `q`. -/
theorem caddW_spec {d : BitVec 16} (h1 : -3329 ≤ d.toInt) (h2 : d.toInt < 3329) :
    (caddW d).toInt = d.toInt % 3329 := by
  rw [caddW, sshiftRight15]
  split
  · rw [show (-1 : BitVec 16) &&& qW = qW by decide, toInt_add16 (by rw [qW_toInt]; omega_arith)
      (by rw [qW_toInt]; omega_arith), qW_toInt]
    omega_arith
  · rw [show d + ((0 : BitVec 16) &&& qW) = d by rw [show (0 : BitVec 16) &&& qW = 0 by decide]; simp]
    omega_arith

/-- `csubW d` is the value of `d ∈ [0, 2q)` modulo `q`. -/
theorem csubW_spec {d : BitVec 16} (h1 : 0 ≤ d.toInt) (h2 : d.toInt < 2 * 3329) :
    (csubW d).toInt = d.toInt % 3329 := by
  have e := toInt_sub16 (a := d) (b := qW) (by rw [qW_toInt]; omega_arith) (by rw [qW_toInt]; omega_arith)
  rw [qW_toInt] at e
  rw [csubW, caddW_spec (d := d - qW) (by rw [e]; omega_arith) (by rw [e]; omega_arith), e]
  omega_arith

/-! ## Coefficients -/

open VG.Spec.MlKem (Zq)

theorem toInt_of_lt {a : BitVec 16} (h : a.toNat < 3329) : a.toInt = a.toNat := by
  rw [toInt16, ite_eq_left_of_eq_true _ _ (by simp; omega_arith)]

theorem toNat_of_toInt {a : BitVec 16} (h : 0 ≤ a.toInt) : (a.toNat : Int) = a.toInt := by
  rw [toInt16] at h ⊢; have := a.isLt; split at h <;> [rw [ite_eq_left_of_eq_true _ _ (by simp; omega_arith)]; omega_arith]

/-- Cancelling `2¹⁶` modulo `q`: `2¹⁶ · 169 ≡ 1 (mod q)`. -/
theorem cancel_R {r P Y : Int} (h1 : (r * 65536 - P) % 3329 = 0) (h2 : (P - Y * 65536) % 3329 = 0) :
    r % 3329 = Y % 3329 := by
  omega_arith

/-- `b · (ζ · 2¹⁶ mod q) ≡ y · ζ · 2¹⁶ (mod q)` for `b ≡ y (mod q)`. -/
theorem mul_zm {b y ζ z : Int} (hby : (b - y) % 3329 = 0) (hz : z = ζ * 65536 % 3329) :
    (b * z - y * ζ * 65536) % 3329 = 0 := by
  have e : b * z - y * ζ * 65536 = (b - y) * z + y * (z - ζ * 65536) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_assoc y ζ]; omega_arith
  rw [e]
  apply Int.emod_eq_zero_of_dvd
  refine Int.dvd_add (Int.dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hby))
    (Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero ?_))
  rw [hz]; omega_arith

/-- `ζ · y mod q`, from a word `b ≡ y (mod q)` in `(-q, q)` and the word
`ζ · 2¹⁶ mod q`. -/
theorem mulZ_spec {b z : BitVec 16} {y ζ : Zq} (hb1 : -3329 < b.toInt) (hb2 : b.toInt < 3329)
    (hby : (b.toInt - (y.val : Int)) % 3329 = 0) (hz : z.toNat = ζ.val * 65536 % 3329) :
    (caddW (montW b z)).toInt = (ζ * y).val := by
  have hzl : z.toNat < 3329 := by rw [hz]; exact Nat.mod_lt _ (by decide)
  have hzi := toInt_of_lt hzl
  have hn : (b.toInt * z.toInt).natAbs ≤ 3328 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have h1 := Int.le_natAbs (a := b.toInt * z.toInt)
  have h2 := Int.le_natAbs (a := -(b.toInt * z.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := montW_spec (d := b) (z := z) (by omega_arith) (by omega_arith)
  have hzI : z.toInt = (ζ.val : Int) * 65536 % 3329 := by rw [hzi]; omega_arith
  have hm := mul_zm (ζ := (ζ.val : Int)) hby hzI
  rw [caddW_spec (Int.le_of_lt m1) m2, val_mul, cancel_R m3 hm, Int.natCast_emod, Int.natCast_mul,
    Int.mul_comm (ζ.val : Int)]
  rfl

/-- The value modulo `q` of a sum or a difference of two words less than `q`. -/
theorem addsub_int {A T : Int} (hA : 0 ≤ A ∧ A < 3329) (hT : 0 ≤ T ∧ T < 3329) :
    (-32768 ≤ A + T ∧ A + T < 32768 ∧ 0 ≤ A + T ∧ A + T < 2 * 3329) ∧
      (-32768 ≤ A - T ∧ A - T < 32768 ∧ -3329 ≤ A - T ∧ A - T < 3329) := by
  omega_arith

/-- The two words of a butterfly of Algorithm 9 (`vbfly`): `x + ζ y` and
`x - ζ y`, from the words `x`, `y` and `ζ · 2¹⁶ mod q`. -/
theorem bflyW {a b z : BitVec 16} {x y ζ : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 65536 % 3329) :
    (csubW (a + caddW (montW b z))).toNat = (x + ζ * y).val ∧
      (caddW (a - caddW (montW b z))).toNat = (x - ζ * y).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  have ht := mulZ_spec (b := b) (y := y) (ζ := ζ) (by rw [bi]; omega_arith) (by rw [bi]; omega_arith)
    (by rw [bi, Int.sub_self]; rfl) hz
  have hzy := val_lt (ζ * y)
  generalize caddW (montW b z) = t at ht
  obtain ⟨⟨p1, p2, p3, p4⟩, ⟨m1, m2, m3, m4⟩⟩ :=
    addsub_int (A := a.toInt) (T := t.toInt) (by rw [ai]; omega_arith)
      (by rw [ht]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hzy⟩)
  rw [← toInt_add16 p1 p2] at p3 p4
  rw [← toInt_sub16 m1 m2] at m3 m4
  have c1 := csubW_spec p3 p4
  have c2 := caddW_spec m3 m4
  rw [toInt_add16 p1 p2] at c1
  rw [toInt_sub16 m1 m2] at c2
  have n1 := toNat_of_toInt (a := csubW (a + t)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  have n2 := toNat_of_toInt (a := caddW (a - t)) (by rw [c2]; exact Int.emod_nonneg _ (by decide))
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
    (csubW (a + b)).toNat = (x + y).val ∧ (caddW (montW (b - a) z)).toNat = (ζ * (y - x)).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  have p1 : -32768 ≤ a.toInt + b.toInt := by rw [ai, bi]; omega_arith
  have p2 : a.toInt + b.toInt < 32768 := by rw [ai, bi]; omega_arith
  have m1 : -32768 ≤ b.toInt - a.toInt := by rw [ai, bi]; omega_arith
  have m2 : b.toInt - a.toInt < 32768 := by rw [ai, bi]; omega_arith
  have c1 := csubW_spec (d := a + b) (by rw [toInt_add16 p1 p2, ai, bi]; omega_arith)
    (by rw [toInt_add16 p1 p2, ai, bi]; omega_arith)
  rw [toInt_add16 p1 p2, ai, bi] at c1
  have n1 := toNat_of_toInt (a := csubW (a + b)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  rw [c1] at n1
  have hm := mulZ_spec (b := b - a) (y := y - x) (ζ := ζ) (by rw [toInt_sub16 m1 m2, ai, bi]; omega_arith)
    (by rw [toInt_sub16 m1 m2, ai, bi]; omega_arith)
    (by
      have v : (y - x).val = (y.val + (3329 - x.val)) % 3329 := val_sub' _ _
      rw [toInt_sub16 m1 m2, ai, bi, v]; omega_arith) hz
  have hzy := val_lt (ζ * (y - x))
  have n2 := toNat_of_toInt (a := caddW (montW (b - a) z)) (by rw [hm]; exact Int.natCast_nonneg _)
  rw [hm] at n2
  have v1 : (x + y).val = (x.val + y.val) % 3329 := val_add' _ _
  rw [v1]
  generalize (ζ * (y - x)).val = Z at *
  generalize x.val = X at *
  generalize y.val = Y at *
  constructor <;> omega_using [n1, n2, hx, hy]

end VG.Proof.MlKem.X86.W

/-! ## Words of XMM registers -/

namespace VG.Proof.MlKem.X86.Vec

open VG VG.X86 VG.X86.Lanes VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.W

theorem cases8 {i : Nat} (hi : i < 8) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  omega_using [hi]

/-- `v` in each doubleword: what `mov eax, v`, `movd`, `pshufd` with 0 leave. -/
def bc (v : BitVec 32) : BitVec 128 := L fun _ => v

theorem bc_eq (v : BitVec 32) : shufDwords ((0 : BitVec 96) ++ v) 0 = bc v := bcast_L v

theorem dword_bc (v : BitVec 32) {i : Nat} (hi : i < 4) : dword (bc v) i = v := dword_L _ hi

theorem word_bc (v : BitVec 32) {i : Nat} (hi : i < 8) : word (bc v) i = v.extractLsb' (16 * (i % 2)) 16 := by
  rw [word_eq_dword, dword_bc _ (by omega_using [hi])]

/-- `q` in each word. -/
def qV : BitVec 128 := bc 0x0D010D01#32

/-- `q⁻¹ mod 2¹⁶` in each word. -/
def qinvV : BitVec 128 := bc 0xF301F301#32

theorem word_qV {i : Nat} (hi : i < 8) : word qV i = qW := by
  rw [qV, word_bc _ hi]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> rfl

theorem word_qinvV {i : Nat} (hi : i < 8) : word qinvV i = qinvW := by
  rw [qinvV, word_bc _ hi]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> rfl

/-- The register `wmont` leaves. -/
def montV (d z : BitVec 128) : BitVec 128 :=
  XBinOp.eval .psubw (pmulhw d z) (pmulhw (pmullw (pmullw d z) qinvV) qV)

theorem word_montV (d z : BitVec 128) {i : Nat} (hi : i < 8) :
    word (montV d z) i = montW (word d i) (word z i) := by
  rw [montV, word_psubw _ _ hi, word_pmulhw _ _ hi, word_pmulhw _ _ hi, word_pmullw _ _ hi, word_pmullw _ _ hi,
    word_qV hi, word_qinvV hi]
  rfl

/-- The register `wcadd` leaves. -/
def caddV (d : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddw d (XBinOp.eval .pand (XShiftOp.eval .psraw d 15) qV)

theorem word_caddV (d : BitVec 128) {i : Nat} (hi : i < 8) : word (caddV d) i = caddW (word d i) := by
  rw [caddV, word_paddw _ _ hi, word_pand, word_psraw _ _ hi, word_qV hi]
  rfl

/-- The register `wcsub` leaves. -/
def csubV (d : BitVec 128) : BitVec 128 := caddV (XBinOp.eval .psubw d qV)

theorem word_csubV (d : BitVec 128) {i : Nat} (hi : i < 8) : word (csubV d) i = csubW (word d i) := by
  rw [csubV, word_caddV _ hi, word_psubw _ _ hi, word_qV hi]
  rfl

/-! ## The butterflies -/

/-- The first results of `fCore`, from the `a`s, the `b`s and the zetas. -/
def fwdS (a b z : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddw a (caddV (montV b z)))

/-- The second results of `fCore`. -/
def fwdD (a b z : BitVec 128) : BitVec 128 := caddV (XBinOp.eval .psubw a (caddV (montV b z)))

/-- The first results of `iCore`. -/
def invS (a b _z : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddw a b)

/-- The second results of `iCore`. -/
def invD (a b z : BitVec 128) : BitVec 128 := caddV (montV (XBinOp.eval .psubw b a) z)

/-- The words of `x` hold the canonical values `f i`. -/
def Lanes (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ i < 8, (word x i).toNat = (f i).val

/-- The words of `x` are the zetas `ζ i` in Montgomery form. -/
def ZLanes (x : BitVec 128) (ζ : Nat → Zq) : Prop := ∀ i < 8, (word x i).toNat = (ζ i).val * 65536 % 3329

theorem fwd_lanes {a b z : BitVec 128} {x y ζ : Nat → Zq} (ha : Lanes a x) (hb : Lanes b y) (hz : ZLanes z ζ) :
    Lanes (fwdS a b z) (fun i => x i + ζ i * y i) ∧ Lanes (fwdD a b z) (fun i => x i - ζ i * y i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [fwdS, word_csubV _ hi, word_paddw _ _ hi, word_caddV _ hi, word_montV _ _ hi]
    exact (bflyW (ha i hi) (hb i hi) (hz i hi)).1
  · rw [fwdD, word_caddV _ hi, word_psubw _ _ hi, word_caddV _ hi, word_montV _ _ hi]
    exact (bflyW (ha i hi) (hb i hi) (hz i hi)).2

theorem inv_lanes {a b z : BitVec 128} {x y ζ : Nat → Zq} (ha : Lanes a x) (hb : Lanes b y) (hz : ZLanes z ζ) :
    Lanes (invS a b z) (fun i => x i + y i) ∧ Lanes (invD a b z) (fun i => ζ i * (y i - x i)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [invS, word_csubV _ hi, word_paddw _ _ hi]
    exact (ibflyW (ha i hi) (hb i hi) (hz i hi)).1
  · rw [invD, word_caddV _ hi, word_montV _ _ hi, word_psubw _ _ hi]
    exact (ibflyW (ha i hi) (hb i hi) (hz i hi)).2

/-! ## Sixteen coefficients -/

/-- Position `p` of the sixteen words of `X` and `Y`. -/
def pos (X Y : BitVec 128) (p : Nat) : BitVec 16 := if p < 8 then word X p else word Y (p - 8)

/-- How eight butterflies are computed from two vectors: the registers of
the `a`s and the `b`s (`gA`, `gB`), whose word `e` is at positions `pa e`
and `pb e`, and the vectors stored back from the first and the second
results (`sX`, `sY`). -/
structure Shape where
  gA : BitVec 128 → BitVec 128 → BitVec 128
  gB : BitVec 128 → BitVec 128 → BitVec 128
  sX : BitVec 128 → BitVec 128 → BitVec 128
  sY : BitVec 128 → BitVec 128 → BitVec 128
  pa : Nat → Nat
  pb : Nat → Nat

structure ShapeOk (sh : Shape) : Prop where
  gath : ∀ X Y e, e < 8 → word (sh.gA X Y) e = pos X Y (sh.pa e) ∧ word (sh.gB X Y) e = pos X Y (sh.pb e)
  scat : ∀ S D e, e < 8 →
    pos (sh.sX S D) (sh.sY S D) (sh.pa e) = word S e ∧ pos (sh.sX S D) (sh.sY S D) (sh.pb e) = word D e
  cover : ∀ p < 16, ∃ e < 8, p = sh.pa e ∨ p = sh.pb e
  lt : ∀ e < 8, sh.pa e < 16 ∧ sh.pb e < 16

/-- A layer with `len ≥ 8`: the vector at `[eax]` holds the `a`s and that at `[eax + 2 · len]` the `b`s. -/
def sh8 : Shape where
  gA X _ := X
  gB _ Y := Y
  sX S _ := S
  sY _ D := D
  pa e := e
  pb e := e + 8

theorem sh8_ok : ShapeOk sh8 where
  gath X Y e he := by
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  scat S D e he := by
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  cover := by decide
  lt := by decide

/-- The layer with `len = 4`: two blocks in the vectors at `[eax]` and `[eax + 16]`. -/
def sh4 : Shape where
  gA X Y := XBinOp.eval .punpcklqdq X Y
  gB X Y := XBinOp.eval .punpckhqdq X Y
  sX S D := XBinOp.eval .punpcklqdq S D
  sY S D := XBinOp.eval .punpckhqdq S D
  pa e := if e < 4 then e else e + 4
  pb e := if e < 4 then e + 4 else e + 8

theorem sh4_ok : ShapeOk sh4 where
  gath X Y e he := by
    refine ⟨(word_punpcklqdq X Y he).trans ?_, (word_punpckhqdq X Y he).trans ?_⟩ <;>
      rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  scat S D e he := by
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨word_punpcklqdq S D (i := 0) (by decide), word_punpcklqdq S D (i := 4) (by decide)⟩
    · exact ⟨word_punpcklqdq S D (i := 1) (by decide), word_punpcklqdq S D (i := 5) (by decide)⟩
    · exact ⟨word_punpcklqdq S D (i := 2) (by decide), word_punpcklqdq S D (i := 6) (by decide)⟩
    · exact ⟨word_punpcklqdq S D (i := 3) (by decide), word_punpcklqdq S D (i := 7) (by decide)⟩
    · exact ⟨word_punpckhqdq S D (i := 0) (by decide), word_punpckhqdq S D (i := 4) (by decide)⟩
    · exact ⟨word_punpckhqdq S D (i := 1) (by decide), word_punpckhqdq S D (i := 5) (by decide)⟩
    · exact ⟨word_punpckhqdq S D (i := 2) (by decide), word_punpckhqdq S D (i := 6) (by decide)⟩
    · exact ⟨word_punpckhqdq S D (i := 3) (by decide), word_punpckhqdq S D (i := 7) (by decide)⟩
  cover := by decide
  lt := by decide

theorem word_dword0 (x : BitVec 128) {e : Nat} (he : e < 2) : word x e = (dword x 0).extractLsb' (16 * e) 16 := by
  have := word_dword x 0 e he
  rwa [Nat.mul_zero, Nat.zero_add] at this

/-- Word `e` of doubleword `k`. -/
theorem word_of_dword {x y : BitVec 128} {k j : Nat} (h : dword x k = dword y j) {e : Nat} (he : e < 2) :
    word x (2 * k + e) = word y (2 * j + e) := by
  rw [word_dword _ _ _ he, word_dword _ _ _ he, h]

/-- The words of a register whose doublewords `pshufd` with `0xD8` arranged. -/
theorem word_shufD8 (a : BitVec 128) {e : Nat} (he : e < 2) :
    word (shufDwords a 0xD8) e = word a e ∧ word (shufDwords a 0xD8) (2 + e) = word a (4 + e) ∧
      word (shufDwords a 0xD8) (4 + e) = word a (2 + e) ∧ word (shufDwords a 0xD8) (6 + e) = word a (6 + e) := by
  have d0 : dword (shufDwords a 0xD8) 0 = dword a 0 := dword_shufDwords a _ (by decide)
  have d1 : dword (shufDwords a 0xD8) 1 = dword a 2 := dword_shufDwords a _ (by decide)
  have d2 : dword (shufDwords a 0xD8) 2 = dword a 1 := dword_shufDwords a _ (by decide)
  have d3 : dword (shufDwords a 0xD8) 3 = dword a 3 := dword_shufDwords a _ (by decide)
  refine ⟨?_, word_of_dword d1 he, word_of_dword d2 he, word_of_dword d3 he⟩
  rw [word_dword0 _ he, word_dword0 _ he, d0]

/-- The words of `punpckldq`. -/
theorem word_punpckldq (a b : BitVec 128) {e : Nat} (he : e < 2) :
    word (XBinOp.eval .punpckldq a b) e = word a e ∧ word (XBinOp.eval .punpckldq a b) (2 + e) = word b e ∧
      word (XBinOp.eval .punpckldq a b) (4 + e) = word a (2 + e) ∧
      word (XBinOp.eval .punpckldq a b) (6 + e) = word b (2 + e) := by
  rw [punpckldq_eq]
  have d0 : dword (ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)) 0 = dword a 0 := dword_ofDwords_0 ..
  have d1 : dword (ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)) 1 = dword b 0 := dword_ofDwords_1 ..
  have d2 : dword (ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)) 2 = dword a 1 := dword_ofDwords_2 ..
  have d3 : dword (ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)) 3 = dword b 1 := dword_ofDwords_3 ..
  refine ⟨?_, ?_, word_of_dword d2 he, word_of_dword d3 he⟩
  · rw [word_dword0 _ he, word_dword0 _ he, d0]
  · rw [word_dword0 b he]; exact (word_dword _ 1 _ he).trans (by rw [d1])

/-- The words of `punpckhdq`. -/
theorem word_punpckhdq (a b : BitVec 128) {e : Nat} (he : e < 2) :
    word (XBinOp.eval .punpckhdq a b) e = word a (4 + e) ∧ word (XBinOp.eval .punpckhdq a b) (2 + e) = word b (4 + e) ∧
      word (XBinOp.eval .punpckhdq a b) (4 + e) = word a (6 + e) ∧
      word (XBinOp.eval .punpckhdq a b) (6 + e) = word b (6 + e) := by
  rw [punpckhdq_eq]
  have d0 : dword (ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)) 0 = dword a 2 := dword_ofDwords_0 ..
  have d1 : dword (ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)) 1 = dword b 2 := dword_ofDwords_1 ..
  have d2 : dword (ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)) 2 = dword a 3 := dword_ofDwords_2 ..
  have d3 : dword (ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)) 3 = dword b 3 := dword_ofDwords_3 ..
  refine ⟨?_, word_of_dword d1 he, word_of_dword d2 he, word_of_dword d3 he⟩
  rw [word_dword0 _ he, d0]; exact (word_dword _ 2 _ he).symm

/-- The layer with `len = 2`: four blocks in the vectors at `[eax]` and `[eax + 16]`. -/
def sh2 : Shape where
  gA X Y := XBinOp.eval .punpcklqdq (shufDwords X 0xD8) (shufDwords Y 0xD8)
  gB X Y := XBinOp.eval .punpckhqdq (shufDwords X 0xD8) (shufDwords Y 0xD8)
  sX S D := XBinOp.eval .punpckldq S D
  sY S D := XBinOp.eval .punpckhdq S D
  pa e := 4 * (e / 2) + e % 2
  pb e := 4 * (e / 2) + e % 2 + 2

theorem sh2_ok : ShapeOk sh2 where
  gath X Y e he := by
    obtain ⟨x0, x1, x2, x3⟩ := word_shufD8 X (e := 0) (by decide)
    obtain ⟨x0', x1', x2', x3'⟩ := word_shufD8 X (e := 1) (by decide)
    obtain ⟨y0, y1, y2, y3⟩ := word_shufD8 Y (e := 0) (by decide)
    obtain ⟨y0', y1', y2', y3'⟩ := word_shufD8 Y (e := 1) (by decide)
    have l := fun i (hi : i < 8) => word_punpcklqdq (shufDwords X 0xD8) (shufDwords Y 0xD8) hi
    have h := fun i (hi : i < 8) => word_punpckhqdq (shufDwords X 0xD8) (shufDwords Y 0xD8) hi
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(l 0 (by decide)).trans x0, (h 0 (by decide)).trans x2⟩
    · exact ⟨(l 1 (by decide)).trans x0', (h 1 (by decide)).trans x2'⟩
    · exact ⟨(l 2 (by decide)).trans x1, (h 2 (by decide)).trans x3⟩
    · exact ⟨(l 3 (by decide)).trans x1', (h 3 (by decide)).trans x3'⟩
    · exact ⟨(l 4 (by decide)).trans y0, (h 4 (by decide)).trans y2⟩
    · exact ⟨(l 5 (by decide)).trans y0', (h 5 (by decide)).trans y2'⟩
    · exact ⟨(l 6 (by decide)).trans y1, (h 6 (by decide)).trans y3⟩
    · exact ⟨(l 7 (by decide)).trans y1', (h 7 (by decide)).trans y3'⟩
  scat S D e he := by
    obtain ⟨l0, l1, l2, l3⟩ := word_punpckldq S D (e := 0) (by decide)
    obtain ⟨l0', l1', l2', l3'⟩ := word_punpckldq S D (e := 1) (by decide)
    obtain ⟨h0, h1, h2, h3⟩ := word_punpckhdq S D (e := 0) (by decide)
    obtain ⟨h0', h1', h2', h3'⟩ := word_punpckhdq S D (e := 1) (by decide)
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨l0, l1⟩
    · exact ⟨l0', l1'⟩
    · exact ⟨l2, l3⟩
    · exact ⟨l2', l3'⟩
    · exact ⟨h0, h1⟩
    · exact ⟨h0', h1'⟩
    · exact ⟨h2, h3⟩
    · exact ⟨h2', h3'⟩
  cover := by decide
  lt := by decide

/-- The vector a body stores at `[eax]`: `FS` and `FD` are the results of its butterflies. -/
def bodyX (sh : Shape) (FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) (X Y Z : BitVec 128) :
    BitVec 128 :=
  sh.sX (FS (sh.gA X Y) (sh.gB X Y) Z) (FD (sh.gA X Y) (sh.gB X Y) Z)

/-- The vector a body stores at `[eax + d]`. -/
def bodyY (sh : Shape) (FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) (X Y Z : BitVec 128) :
    BitVec 128 :=
  sh.sY (FS (sh.gA X Y) (sh.gB X Y) Z) (FD (sh.gA X Y) (sh.gB X Y) Z)

/-- The results `FS` and `FD` of eight butterflies are `sS` and `sD` of the
coefficients, with the zetas. -/
def CoreLanes (FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) (sS sD : Zq → Zq → Zq → Zq) : Prop :=
  ∀ (a b z : BitVec 128) (x y ζ : Nat → Zq), Lanes a x → Lanes b y → ZLanes z ζ →
    Lanes (FS a b z) (fun i => sS (x i) (y i) (ζ i)) ∧ Lanes (FD a b z) (fun i => sD (x i) (y i) (ζ i))

theorem fwd_core : CoreLanes fwdS fwdD (fun x y ζ => x + ζ * y) (fun x y ζ => x - ζ * y) :=
  fun _ _ _ _ _ _ ha hb hz => fwd_lanes ha hb hz

theorem inv_core : CoreLanes invS invD (fun x y _ => x + y) (fun x y ζ => ζ * (y - x)) :=
  fun _ _ _ _ _ _ ha hb hz => inv_lanes ha hb hz

/-- The vectors `FX X Y Z` and `FY X Y Z` hold what the butterflies of the
positions leave: from the coefficients of `f` (`idx p` at position `p`),
with the zetas `ζ e` in Montgomery form in the words of `Z`, those of `G`,
whose pairs are `sS` and `sD` of those of `f`. -/
def NewOk (sh : Shape) (FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128)
    (sS sD : Zq → Zq → Zq → Zq) : Prop :=
  ∀ (f G : Poly) (idx : Nat → Nat) (Z : BitVec 128) (ζ : Nat → Zq), ZLanes Z ζ →
    (∀ e < 8, G[idx (sh.pa e)]! = sS f[idx (sh.pa e)]! f[idx (sh.pb e)]! (ζ e) ∧
      G[idx (sh.pb e)]! = sD f[idx (sh.pa e)]! f[idx (sh.pb e)]! (ζ e)) →
    ∀ X Y, (∀ p < 16, (pos X Y p).toNat = (f[idx p]!).val) →
      ∀ p < 16, (pos (FX X Y Z) (FY X Y Z) p).toNat = (G[idx p]!).val

theorem body_new (sh : Shape) (ok : ShapeOk sh) {FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    {sS sD : Zq → Zq → Zq → Zq} (hc : CoreLanes FS FD sS sD) :
    NewOk sh (bodyX sh FS FD) (bodyY sh FS FD) sS sD := by
  intro f G idx Z ζ hz hG X Y hV p hp
  obtain ⟨e, he, hpe⟩ := ok.cover p hp
  obtain ⟨sa, sb⟩ := ok.scat (FS (sh.gA X Y) (sh.gB X Y) Z) (FD (sh.gA X Y) (sh.gB X Y) Z) e he
  have hA : Lanes (sh.gA X Y) (fun i => f[idx (sh.pa i)]!) := fun i hi => by
    rw [(ok.gath X Y i hi).1]; exact hV _ (ok.lt i hi).1
  have hB : Lanes (sh.gB X Y) (fun i => f[idx (sh.pb i)]!) := fun i hi => by
    rw [(ok.gath X Y i hi).2]; exact hV _ (ok.lt i hi).2
  obtain ⟨hS, hD⟩ := hc _ _ Z _ _ ζ hA hB hz
  rcases hpe with rfl | rfl
  · rw [bodyX, bodyY, sa, (hG e he).1]; exact hS e he
  · rw [bodyX, bodyY, sb, (hG e he).2]; exact hD e he

end VG.Proof.MlKem.X86.Vec
