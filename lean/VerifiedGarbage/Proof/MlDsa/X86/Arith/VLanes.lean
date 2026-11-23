module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.MlDsa.Arith.Mont
public import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA on x86 (32-bit): arithmetic modulo `q` in the doublewords of an XMM register

What the pieces of vector code of `Impl/MlDsa/X86/Arith/Mul.lean` leave in
each doubleword, as x86-64's `Proof/MlDsa/X86_64/Arith/VLanes.lean` does for
its registers:

* `montV d z`, the register `vmont` leaves: doubleword `i` is `mont` of the
  product of doubleword `i` of `d` and the even doubleword of `z` in the
  same quadword (`dword_montV`), if each product is less than `q · 2³²`
  (each quadword product `P` becomes `P + m · q`, which is `mont P · 2³²`:
  `redc_toNat`); `mont2V d b`, the register `vmont2` leaves, multiplies
  doubleword by doubleword (`dword_mont2V`);
* `csubL`, the conditional subtraction of `q` with the model's
  instructions (no `psubd`, no `psrad`): `y = d + (2³² - q)`, whose sign bit
  is set exactly when `d < q`, and `y + (¬((y >> 31) + 0xFFFFFFFF) ∧ q)`
  (`csubL_toNat`);
* `subL a b c`, `a - b + c` as `a + (c + 1) + (b xor 0xFFFFFFFF)`
  (`subL_toNat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.X86.Lanes
open VG.Proof.MlDsa.Arith
open VG.Proof.Mont.X86.Sse2 (qword_paddq qword_psrlq qword_pmuludq_0 qword_pmuludq_1 dword_psrlq_0 dword_psrlq_2
  qword_append_0 qword_append_1)
open VG.Spec.MlDsa (q)

/-! ## Quadwords -/

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

theorem qword_pmuludq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (pmuludq x y) i = lo32 (qword x i) * lo32 (qword y i) := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
  · rw [qword_pmuludq_0, lo32, lo32, ← dword_lo, ← dword_lo]
  · rw [qword_pmuludq_1, lo32, lo32, ← dword_lo, ← dword_lo]

theorem toNat_lo32_mul (x y : BitVec 64) : (lo32 x * lo32 y).toNat = x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) := by
  rw [BitVec.toNat_mul, lo32_toNat, lo32_toNat]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by decide)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h1 h2) (by decide))

theorem toNat_qword_pmuludq (x y : BitVec 128) {j : Nat} (hj : j < 2) :
    (qword (pmuludq x y) j).toNat = (dword x (2 * j)).toNat * (dword y (2 * j)).toNat := by
  rw [qword_pmuludq _ _ hj, toNat_lo32_mul, dword_lo, dword_lo, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero]

/-- The odd doubleword of a quadword, moved down by `psrlq`. -/
theorem dword_psrlq_even (a : BitVec 128) {j : Nat} (hj : j < 2) :
    dword (XShiftOp.eval .psrlq a 32) (2 * j) = dword a (2 * j + 1) := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
  · exact dword_psrlq_0 a
  · exact dword_psrlq_2 a

/-! ## Montgomery reduction of a quadword -/

/-- `v` in each doubleword: what `mov eax, v`, `movd`, `pshufd` with 0 leave. -/
def bc (v : BitVec 32) : BitVec 128 := L fun _ => v

theorem bc_eq (v : BitVec 32) : shufDwords ((0 : BitVec 96) ++ v) 0 = bc v := bcast_L v

theorem dword_bc (v : BitVec 32) {i : Nat} (hi : i < 4) : dword (bc v) i = v := dword_L _ hi

/-- `q` in each doubleword. -/
def qV : BitVec 128 := bc 8380417#32

/-- `-q⁻¹ mod 2³²` in each doubleword. -/
def nqiV : BitVec 128 := bc 4236238847#32

theorem lo32_qword {x : BitVec 128} {v : BitVec 32} (h : ∀ i < 4, dword x i = v) {j : Nat} (hj : j < 2) :
    (lo32 (qword x j)).toNat = v.toNat := by
  rw [lo32_toNat, ← h (2 * j) (by omega_using [hj]), dword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem lo32_qword_qV {j : Nat} (hj : j < 2) : (lo32 (qword qV j)).toNat = q :=
  lo32_qword (fun _ hi => dword_bc _ hi) hj

theorem lo32_qword_nqiV {j : Nat} (hj : j < 2) : (lo32 (qword nqiV j)).toNat = montQInv :=
  lo32_qword (fun _ hi => dword_bc _ hi) hj

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

/-! ## `vmont` and `vmont2` -/

/-- What `vredc` leaves of the quadword products `a`. -/
def redcV (a : BitVec 128) : BitVec 128 := XBinOp.eval .paddq a (pmuludq (pmuludq a nqiV) qV)

theorem qword_redcV (a : BitVec 128) {j : Nat} (hj : j < 2) :
    qword (redcV a) j = redc (qword a j) (qword nqiV j) (qword qV j) := by
  rw [redcV, qword_paddq _ _ hj, qword_pmuludq _ _ hj, qword_pmuludq _ _ hj]; rfl

/-- The two reduced quadword products `a` (of the even doublewords) and `b`
(of the odd ones) as four doublewords. -/
def joinV (a b : BitVec 128) : BitVec 128 :=
  XBinOp.eval .por (XShiftOp.eval .psrlq (redcV a) 32) (redcV b)

theorem dword_joinV {a b : BitVec 128} (ha : ∀ j < 2, (qword a j).toNat < q * 2 ^ 32)
    (hb : ∀ j < 2, (qword b j).toNat < q * 2 ^ 32) {j : Nat} (hj : j < 2) :
    (dword (joinV a b) (2 * j)).toNat = mont (qword a j).toNat ∧
      (dword (joinV a b) (2 * j + 1)).toNat = mont (qword b j).toNat := by
  have hqi := lo32_qword_nqiV hj
  have hqq := lo32_qword_qV hj
  refine ⟨?_, ?_⟩
  · rw [joinV, dword_por, dword_lo, dword_lo, qword_psrlq _ hj, qword_redcV _ hj, qword_redcV _ hj,
      redc_lo hqi hqq (hb j hj), or_zero_toNat, lo_shr32, redc_hi hqi hqq (ha j hj)]
  · rw [joinV, dword_por, dword_hi, dword_hi, qword_psrlq _ hj, hi_shr32, zero_or_toNat, qword_redcV _ hj,
      redc_hi hqi hqq (hb j hj)]

/-- The register `vmont d z` leaves in `d`. -/
def montV (d z : BitVec 128) : BitVec 128 :=
  joinV (pmuludq d z) (pmuludq (XShiftOp.eval .psrlq d 32) z)

/-- Each doubleword of `montV d z` is `mont` of the product of that of `d`
and the even doubleword of `z` in its quadword. -/
theorem dword_montV {d z : BitVec 128}
    (hb : ∀ i < 4, (dword d i).toNat * (dword z (2 * (i / 2))).toNat < q * 2 ^ 32) {i : Nat} (hi : i < 4) :
    (dword (montV d z) i).toNat = mont ((dword d i).toNat * (dword z (2 * (i / 2))).toNat) := by
  have hx : ∀ j < 2, (qword (pmuludq d z) j).toNat = (dword d (2 * j)).toNat * (dword z (2 * j)).toNat :=
    fun j hj => toNat_qword_pmuludq d z hj
  have hy : ∀ j < 2, (qword (pmuludq (XShiftOp.eval .psrlq d 32) z) j).toNat =
      (dword d (2 * j + 1)).toNat * (dword z (2 * j)).toNat := fun j hj => by
    rw [toNat_qword_pmuludq _ _ hj, dword_psrlq_even _ hj]
  have ha : ∀ j < 2, (qword (pmuludq d z) j).toNat < q * 2 ^ 32 := fun j hj => by
    rw [hx j hj]
    have := hb (2 * j) (by omega_using [hj])
    rwa [show 2 * j / 2 = j by omega_using []] at this
  have hb' : ∀ j < 2, (qword (pmuludq (XShiftOp.eval .psrlq d 32) z) j).toNat < q * 2 ^ 32 := fun j hj => by
    rw [hy j hj]
    have := hb (2 * j + 1) (by omega_using [hj])
    rwa [show (2 * j + 1) / 2 = j by omega_using []] at this
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j < 2, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega_using [hi], by omega_using []⟩
  · rw [montV, (dword_joinV ha hb' hj).1, hx j hj, show 2 * j / 2 = j by omega_using []]
  · rw [montV, (dword_joinV ha hb' hj).2, hy j hj, show (2 * j + 1) / 2 = j by omega_using []]

/-- The register `vmont2 d b` leaves in `d`. -/
def mont2V (d b : BitVec 128) : BitVec 128 :=
  joinV (pmuludq d b) (pmuludq (XShiftOp.eval .psrlq d 32) (XShiftOp.eval .psrlq b 32))

/-- Each doubleword of `mont2V d b` is `mont` of the product of those of `d` and `b`. -/
theorem dword_mont2V {d b : BitVec 128} (hb : ∀ i < 4, (dword d i).toNat * (dword b i).toNat < q * 2 ^ 32)
    {i : Nat} (hi : i < 4) : (dword (mont2V d b) i).toNat = mont ((dword d i).toNat * (dword b i).toNat) := by
  have hx : ∀ j < 2, (qword (pmuludq d b) j).toNat = (dword d (2 * j)).toNat * (dword b (2 * j)).toNat :=
    fun j hj => toNat_qword_pmuludq d b hj
  have hy : ∀ j < 2, (qword (pmuludq (XShiftOp.eval .psrlq d 32) (XShiftOp.eval .psrlq b 32)) j).toNat =
      (dword d (2 * j + 1)).toNat * (dword b (2 * j + 1)).toNat := fun j hj => by
    rw [toNat_qword_pmuludq _ _ hj, dword_psrlq_even _ hj, dword_psrlq_even _ hj]
  have ha : ∀ j < 2, (qword (pmuludq d b) j).toNat < q * 2 ^ 32 := fun j hj => by
    rw [hx j hj]; exact hb (2 * j) (by omega_using [hj])
  have hb' : ∀ j < 2, (qword (pmuludq (XShiftOp.eval .psrlq d 32) (XShiftOp.eval .psrlq b 32)) j).toNat <
      q * 2 ^ 32 := fun j hj => by
    rw [hy j hj]; exact hb (2 * j + 1) (by omega_using [hj])
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j < 2, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega_using [hi], by omega_using []⟩
  · rw [mont2V, (dword_joinV ha hb' hj).1, hx j hj]
  · rw [mont2V, (dword_joinV ha hb' hj).2, hy j hj]

/-! ## The conditional subtraction of `q`, and subtractions -/

/-- `q` as a doubleword. -/
def qB : BitVec 32 := 8380417#32

/-- `2³² - q` as a doubleword. -/
def negqB : BitVec 32 := 4286586879#32

/-- `0xFFFFFFFF` in each doubleword. -/
def onesV : BitVec 128 := bc 4294967295#32

/-- `2³² - q` in each doubleword. -/
def negqV : BitVec 128 := bc negqB

/-- `vcsub` on a doubleword. -/
def csubL (d : BitVec 32) : BitVec 32 :=
  d + negqB + (~~~((d + negqB) >>> 31 + 4294967295#32) &&& qB)

/-- `vcsub` reduces a doubleword less than `2q`. -/
theorem csubL_toNat {d : BitVec 32} (h : d.toNat < 2 * q) : (csubL d).toNat = condSub d.toNat := by
  rw [q_eq] at h
  have e : (d + negqB).toNat = (d.toNat + 4286586879) % 2 ^ 32 := by rw [BitVec.toNat_add]; rfl
  by_cases hq : d.toNat < 8380417
  · have e1 : (d + negqB).toNat = d.toNat + 4286586879 := by rw [e]; omega_using [hq]
    have e2 : (d + negqB) >>> 31 = 1#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e1]
      show _ = 1; omega_using [hq]
    rw [csubL, e2, show ~~~((1#32 : BitVec 32) + 4294967295#32) &&& qB = qB by decide, BitVec.toNat_add, e1,
      condSub, q_eq, ite_eq_right (by omega_using [hq])]
    show (d.toNat + 4286586879 + 8380417) % 2 ^ 32 = d.toNat
    omega_using [hq]
  · have e1 : (d + negqB).toNat = d.toNat - 8380417 := by rw [e]; omega_using [hq, h]
    have e2 : (d + negqB) >>> 31 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e1]
      show _ = 0; omega_using [hq, h]
    rw [csubL, e2, show ~~~((0#32 : BitVec 32) + 4294967295#32) &&& qB = 0#32 by decide, BitVec.add_zero, e1,
      condSub, q_eq, ite_eq_left (by omega_using [hq])]

/-- What `vcsub` leaves of `d`. -/
def csubV (d : BitVec 128) : BitVec 128 :=
  let y := XBinOp.eval .paddd d negqV
  XBinOp.eval .paddd y (XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld y 31) onesV) qV)

theorem dword_pandn (a b : BitVec 128) {k : Nat} (hk : k < 4) :
    dword (XBinOp.eval .pandn a b) k = ~~~dword a k &&& dword b k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj, show 32 * k + j < 128 by omega_using [hk, hj]]

theorem dword_csubV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (csubV d) i = csubL (dword d i) := by
  simp only [csubV, dword_paddd _ _ hi, dword_pandn _ _ hi, dword_psrld _ _ (show (31 : BitVec 8).toNat < 32 by decide) hi,
    negqV, onesV, qV, dword_bc _ hi]
  rfl

/-- `a - b + c` on a doubleword, with `c + 1` as `c1`. -/
def subL (a b c1 : BitVec 32) : BitVec 32 := a + c1 + (b ^^^ 4294967295#32)

theorem subL_toNat {a b c1 : BitVec 32} {c : Nat} (hc : c1.toNat = c + 1) (hb : b.toNat ≤ a.toNat + c)
    (h : a.toNat + c < 2 ^ 32) : (subL a b c1).toNat = a.toNat + c - b.toNat := by
  have hx : (b ^^^ 4294967295#32).toNat = 2 ^ 32 - 1 - b.toNat := by
    rw [show (4294967295#32 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes, BitVec.toNat_not]
  have hbl := b.isLt
  rw [subL, BitVec.toNat_add, BitVec.toNat_add, hc, hx]
  omega_using [hb, h, hbl]

end VG.Proof.MlDsa.X86.Arith
