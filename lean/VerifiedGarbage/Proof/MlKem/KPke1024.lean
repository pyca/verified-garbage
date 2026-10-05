import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Spec.MlKem.Contract
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Spec.Sha3.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Mem`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arith`. -/
section

/-!
# ML-KEM: arithmetic modulo `q`, for every target

Facts about `ℤ_q` (`Fin q`) as the natural numbers that represent its
elements, and recipes that implementations reduce modulo `q = 3329` with, each
proven for every input in its range:

* addition and subtraction of reduced values, with one conditional
  subtraction of `q` (`val_add`, `val_sub`, `condSub`);
* `barrett32`, a Barrett reduction whose products fit in 32 bits (for
  targets with only a 32-bit multiply, such as ARMv7), of any `x < 2²⁵`: a
  sum of two products of reduced values, such as `BaseCaseMultiply`
  computes, is less than `2q² < 2²⁵`;
* `barrett64`, a Barrett reduction with one 32×32→64-bit product, of any
  `x < 2³²`.

Each leaves a value less than `2q` congruent to `x`, which `condSub` then
reduces (`reduce32`, `reduce64`).

It also has the coefficients of polynomials (`getElem!_eq`, `ext_getElem!`)
and of their sums and differences (`add_get`, `sub_get`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## `ℤ_q` as natural numbers -/

theorem val_ofNat (x : Nat) : (ofNat x).val = x % q := rfl

theorem ofNat_val (a : Zq) : ofNat a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem ofNat_of_lt {x : Nat} (h : x < q) : (ofNat x).val = x := Nat.mod_eq_of_lt h

theorem ofNat_mod (x : Nat) : ofNat (x % q) = ofNat x := Fin.ext (Nat.mod_mod _ _)

theorem ofNat_eq_iff {x y : Nat} : ofNat x = ofNat y ↔ x % q = y % q :=
  ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

theorem val_add' (a b : Zq) : (a + b).val = (a.val + b.val) % q := Fin.val_add a b

theorem val_sub' (a b : Zq) : (a - b).val = (a.val + (q - b.val)) % q := by
  rw [Fin.val_sub, Nat.add_comm]

theorem val_mul (a b : Zq) : (a * b).val = a.val * b.val % q := Fin.val_mul a b

theorem val_pow (a : Zq) (k : Nat) : (a ^ k).val = a.val ^ k % q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (a ^ k * a).val = _
    rw [VG.Proof.MlKem.val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

theorem ofNat_add (x y : Nat) : ofNat (x + y) = ofNat x + ofNat y :=
  Fin.ext (by rw [VG.Proof.MlKem.val_add', VG.Proof.MlKem.val_ofNat, VG.Proof.MlKem.val_ofNat, VG.Proof.MlKem.val_ofNat, Nat.add_mod])

theorem ofNat_mul (x y : Nat) : ofNat (x * y) = ofNat x * ofNat y :=
  Fin.ext (by rw [VG.Proof.MlKem.val_mul, VG.Proof.MlKem.val_ofNat, VG.Proof.MlKem.val_ofNat, VG.Proof.MlKem.val_ofNat, Nat.mul_mod])

theorem q_eq : q = 3329 := rfl

/-- The integer that represents an element of `ℤ_q` is less than 3329. -/
theorem val_lt (a : Zq) : a.val < 3329 := a.isLt

theorem val_zero : (0 : Zq).val = 0 := rfl

theorem zero_add' (a : Zq) : 0 + a = a := Fin.ext (by rw [VG.Proof.MlKem.val_add', VG.Proof.MlKem.val_zero, Nat.zero_add,
  Nat.mod_eq_of_lt a.isLt])

/-! ## Coefficients of polynomials -/

theorem n_eq : n = 256 := rfl

theorem getElem!_eq (f : Poly) {i : Nat} (hi : i < n) : f[i]! = f[i] := getElem!_pos f i hi

theorem getElem!_set!_self (f : Poly) {i : Nat} (hi : i < n) (x : Zq) : (f.set! i x)[i]! = x := by
  rw [VG.Proof.MlKem.getElem!_eq _ hi, Vector.getElem_set!, ite_eq_left rfl]

theorem getElem!_set!_ne (f : Poly) {i j : Nat} (hj : j < n) (h : i ≠ j) (x : Zq) :
    (f.set! i x)[j]! = f[j]! := by
  rw [VG.Proof.MlKem.getElem!_eq _ hj, VG.Proof.MlKem.getElem!_eq _ hj, Vector.getElem_set!, ite_eq_right h]

theorem ext_getElem! {f g : Poly} (h : ∀ i < n, f[i]! = g[i]!) : f = g :=
  Vector.ext fun i hi => by rw [← VG.Proof.MlKem.getElem!_eq f hi, ← VG.Proof.MlKem.getElem!_eq g hi]; exact h i hi

theorem add_get (f g : Poly) {i : Nat} (hi : i < n) : (add f g)[i]! = f[i]! + g[i]! := by
  rw [VG.Proof.MlKem.getElem!_eq _ hi, VG.Proof.MlKem.getElem!_eq _ hi, VG.Proof.MlKem.getElem!_eq _ hi]
  simp only [add, Vector.getElem_zipWith]

theorem sub_get (f g : Poly) {i : Nat} (hi : i < n) : (VG.Spec.MlKem.sub f g)[i]! = f[i]! - g[i]! := by
  rw [VG.Proof.MlKem.getElem!_eq _ hi, VG.Proof.MlKem.getElem!_eq _ hi, VG.Proof.MlKem.getElem!_eq _ hi]
  simp only [VG.Spec.MlKem.sub, Vector.getElem_zipWith]

theorem zero_get {i : Nat} (hi : i < n) : zero[i]! = 0 := by
  rw [VG.Proof.MlKem.getElem!_eq _ hi]
  simp only [zero, Vector.getElem_replicate]

theorem zero_add_poly (f : Poly) : add zero f = f :=
  VG.Proof.MlKem.ext_getElem! fun i hi => by rw [VG.Proof.MlKem.add_get _ _ hi, VG.Proof.MlKem.zero_get hi, VG.Proof.MlKem.zero_add']

/-! ## Addition and subtraction of reduced values -/

/-- One conditional subtraction of `q`. -/
def condSub (t : Nat) : Nat := if q ≤ t then t - q else t

/-- One conditional subtraction reduces a value less than `2q`. -/
theorem condSub_eq {t : Nat} (h : t < 2 * q) : VG.Proof.MlKem.condSub t = t % q := by
  unfold VG.Proof.MlKem.condSub; rw [VG.Proof.MlKem.q_eq] at *; split <;> omega

theorem condSub_lt {t : Nat} (h : t < 2 * q) : VG.Proof.MlKem.condSub t < q := by
  unfold VG.Proof.MlKem.condSub; rw [VG.Proof.MlKem.q_eq] at *; split <;> omega

/-- `(a + b) mod q`, for reduced `a` and `b`: `a + b`, less `q` if that is
at least `q`. -/
theorem add_mod_q {a b : Nat} (ha : a < q) (hb : b < q) : (a + b) % q = VG.Proof.MlKem.condSub (a + b) :=
  (VG.Proof.MlKem.condSub_eq (by omega)).symm

/-- `(a - b) mod q`, for reduced `a` and `b`, as `a + q - b` reduced with one
conditional subtraction; that is `a - b` if `b ≤ a`, and `a + q - b`
otherwise. -/
theorem sub_mod_q {a b : Nat} (ha : a < q) (hb : b < q) :
    (a + q - b) % q = VG.Proof.MlKem.condSub (a + q - b) ∧
      VG.Proof.MlKem.condSub (a + q - b) = if b ≤ a then a - b else a + q - b := by
  refine ⟨(VG.Proof.MlKem.condSub_eq (by omega)).symm, ?_⟩
  unfold VG.Proof.MlKem.condSub; rw [VG.Proof.MlKem.q_eq] at *; split <;> split <;> omega

theorem val_add (a b : Zq) : (a + b).val = VG.Proof.MlKem.condSub (a.val + b.val) := by
  rw [VG.Proof.MlKem.val_add', VG.Proof.MlKem.condSub_eq (by have := a.isLt; have := b.isLt; omega)]

theorem val_sub (a b : Zq) : (a - b).val = VG.Proof.MlKem.condSub (a.val + q - b.val) := by
  have := a.isLt; have := b.isLt
  rw [VG.Proof.MlKem.val_sub', VG.Proof.MlKem.condSub_eq (by omega), show a.val + (q - b.val) = a.val + q - b.val by omega]

theorem val_sub_eq (a b : Zq) : (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + q - b.val := by
  rw [VG.Proof.MlKem.val_sub]; exact (VG.Proof.MlKem.sub_mod_q a.isLt b.isLt).2

/-! ## Barrett reduction with 32-bit products -/

/-- The quotient estimate of `barrett32`: `((x >> 11) · 161270) >> 18`,
where `161270 = ⌊2²⁹ / q⌋`. For `x < 2²⁵`, the product is less than `2³²`
(`barrett32_bounds`). -/
def barrett32Quot (x : Nat) : Nat := x / 2048 * 161270 / 262144

/-- `x - ⌊…⌋ · q`: `x` reduced to less than `2q` (`barrett32_lt`). -/
def barrett32 (x : Nat) : Nat := x - VG.Proof.MlKem.barrett32Quot x * q

/-- For `x < 2²⁵`: the product `(x >> 11) · 161270` fits in 32 bits, the
estimate times `q` is at most `x` (so the subtraction does not wrap), and
the estimate times `q` fits in 32 bits. -/
theorem barrett32_bounds {x : Nat} (hx : x < 2 ^ 25) :
    x / 2048 * 161270 < 2 ^ 32 ∧ VG.Proof.MlKem.barrett32Quot x * q ≤ x := by
  unfold VG.Proof.MlKem.barrett32Quot
  rw [VG.Proof.MlKem.q_eq]
  constructor <;> omega

theorem barrett32_lt {x : Nat} (hx : x < 2 ^ 25) : VG.Proof.MlKem.barrett32 x < 2 * q := by
  unfold VG.Proof.MlKem.barrett32 VG.Proof.MlKem.barrett32Quot
  rw [VG.Proof.MlKem.q_eq]
  omega

theorem barrett32_mod {x : Nat} (hx : x < 2 ^ 25) : VG.Proof.MlKem.barrett32 x % q = x % q := by
  have h := (VG.Proof.MlKem.barrett32_bounds hx).2
  unfold VG.Proof.MlKem.barrett32
  generalize VG.Proof.MlKem.barrett32Quot x = e at h
  have := Nat.mul_mod_left e q
  rw [VG.Proof.MlKem.q_eq] at *
  omega

/-- Reduction modulo `q` of `x < 2²⁵` with 32-bit arithmetic. -/
theorem reduce32 {x : Nat} (hx : x < 2 ^ 25) : VG.Proof.MlKem.condSub (VG.Proof.MlKem.barrett32 x) = x % q := by
  rw [VG.Proof.MlKem.condSub_eq (VG.Proof.MlKem.barrett32_lt hx), VG.Proof.MlKem.barrett32_mod hx]

/-! ## Barrett reduction with a 64-bit product -/

/-- The quotient estimate of `barrett64`: `(x · 1290167) >> 32`, where
`1290167 = ⌊2³² / q⌋`. -/
def barrett64Quot (x : Nat) : Nat := x * 1290167 / 4294967296

/-- `x - ⌊…⌋ · q`: `x` reduced to less than `2q` (`barrett64_lt`). -/
def barrett64 (x : Nat) : Nat := x - VG.Proof.MlKem.barrett64Quot x * q

/-- For `x < 2³²`: the product fits in 64 bits, and the estimate times `q`
is at most `x`. -/
theorem barrett64_bounds {x : Nat} (hx : x < 2 ^ 32) :
    x * 1290167 < 2 ^ 64 ∧ VG.Proof.MlKem.barrett64Quot x * q ≤ x := by
  unfold VG.Proof.MlKem.barrett64Quot
  rw [VG.Proof.MlKem.q_eq]
  constructor <;> omega

theorem barrett64_lt {x : Nat} (hx : x < 2 ^ 32) : VG.Proof.MlKem.barrett64 x < 2 * q := by
  unfold VG.Proof.MlKem.barrett64 VG.Proof.MlKem.barrett64Quot
  rw [VG.Proof.MlKem.q_eq]
  omega

theorem barrett64_mod {x : Nat} (hx : x < 2 ^ 32) : VG.Proof.MlKem.barrett64 x % q = x % q := by
  have h := (VG.Proof.MlKem.barrett64_bounds hx).2
  unfold VG.Proof.MlKem.barrett64
  generalize VG.Proof.MlKem.barrett64Quot x = e at h
  have := Nat.mul_mod_left e q
  rw [VG.Proof.MlKem.q_eq] at *
  omega

/-- Reduction modulo `q` of `x < 2³²` with one 64-bit product. -/
theorem reduce64 {x : Nat} (hx : x < 2 ^ 32) : VG.Proof.MlKem.condSub (VG.Proof.MlKem.barrett64 x) = x % q := by
  rw [VG.Proof.MlKem.condSub_eq (VG.Proof.MlKem.barrett64_lt hx), VG.Proof.MlKem.barrett64_mod hx]

/-! ## Products of reduced values -/

/-- A product of reduced values is less than `q² = 11082241`. -/
theorem mul_lt_q2 {a b : Nat} (ha : a < q) (hb : b < q) : a * b < 11082241 :=
  Nat.mul_lt_mul_of_lt_of_lt ha hb

/-- A product of reduced values, reduced with `barrett32`. -/
theorem val_mul_barrett32 (a b : Zq) : (a * b).val = VG.Proof.MlKem.condSub (VG.Proof.MlKem.barrett32 (a.val * b.val)) := by
  rw [VG.Proof.MlKem.val_mul, VG.Proof.MlKem.reduce32 (by have := VG.Proof.MlKem.mul_lt_q2 a.isLt b.isLt; omega)]

/-- `a₀b₀ + a₁b₁γ` of `BaseCaseMultiply`, with `a₁b₁` reduced first: the sum
is less than `2q² < 2²⁵`, so `barrett32` reduces it. -/
theorem val_mul_add_mul (a b c d : Zq) :
    (a * b + c * d).val = VG.Proof.MlKem.condSub (VG.Proof.MlKem.barrett32 (a.val * b.val + c.val * d.val)) := by
  have h1 := VG.Proof.MlKem.mul_lt_q2 a.isLt b.isLt
  have h2 := VG.Proof.MlKem.mul_lt_q2 c.isLt d.isLt
  rw [VG.Proof.MlKem.reduce32 (by omega), VG.Proof.MlKem.val_add', VG.Proof.MlKem.val_mul, VG.Proof.MlKem.val_mul, ← Nat.add_mod]

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Mem`. -/
section

/-!
# ML-KEM: polynomials and bytes in memory, for every target

How the stored representation of `Spec/MlKem/Poly.lean` (a polynomial as
`[u32; 256]`, `coeffAt`, `polyAt`, `Reduced`, `PolyIs`) and `bytesAt` change
when a program writes a coefficient or a byte, and how to conclude `PolyIs` or
`bytesAt … = L` from what each word or byte holds.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Coefficients -/

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (VG.Proof.MlKem.coeffAddr p i) 32 := rfl

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < n) : (VG.Proof.MlKem.polyRegion p).Contains (VG.Proof.MlKem.coeffAddr p i) 4 := by
  rw [VG.Proof.MlKem.n_eq] at hi; exact Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    Mem.Sep (VG.Proof.MlKem.coeffAddr p i) 4 (VG.Proof.MlKem.coeffAddr p j) 4 := by
  rw [VG.Proof.MlKem.n_eq] at hi hj; exact Offset.sep p (by omega) (by omega) (by omega)

theorem coeffAt_writeW_self (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) :
    coeffAt (m.writeW (VG.Proof.MlKem.coeffAddr p i) v) p i = v :=
  Mem.readW_writeW_self32 m _ v

theorem coeffAt_writeW_ne (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j)
    (v : BitVec 32) : coeffAt (m.writeW (VG.Proof.MlKem.coeffAddr p j) v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep (VG.Proof.MlKem.coeff_sep p hi hj h) (by decide)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (v : BitVec 32) :
    coeffAt (m.writeW (VG.Proof.MlKem.coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact VG.Proof.MlKem.coeffAt_writeW_self m p i v
  · exact VG.Proof.MlKem.coeffAt_writeW_ne m p hi hj (Ne.symm ‹_›) v

/-- Writing `w` bits at `a`, apart from coefficient `i`. -/
theorem coeffAt_writeW_sep (m : Mem) (p : Addr) {i : Nat} {a : Addr} {w : Nat} (v : BitVec w)
    (h : Mem.Sep (VG.Proof.MlKem.coeffAddr p i) 4 a (w / 8)) : coeffAt (m.writeW a v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep h (by decide)

/-- Coefficient `i` of `polyAt`: the stored word modulo `q`. -/
theorem polyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i]! = ofNat (coeffAt m p i).toNat := by
  rw [VG.Proof.MlKem.getElem!_eq _ hi]
  simp only [polyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]!).val = (coeffAt m p i).toNat := by
  rw [VG.Proof.MlKem.polyAt_get m p hi, VG.Proof.MlKem.ofNat_of_lt (hr i hi)]

/-- The polynomial after writing coefficient `j`. -/
theorem polyAt_writeW (m : Mem) (p : Addr) {j : Nat} (hj : j < n) (v : BitVec 32) :
    polyAt (m.writeW (VG.Proof.MlKem.coeffAddr p j) v) p = (polyAt m p).set! j (ofNat v.toNat) := by
  refine VG.Proof.MlKem.ext_getElem! fun i hi => ?_
  rw [VG.Proof.MlKem.polyAt_get _ _ hi, VG.Proof.MlKem.coeffAt_writeW m p hi hj]
  split
  · subst j; rw [VG.Proof.MlKem.getElem!_set!_self _ hi]
  · rw [VG.Proof.MlKem.getElem!_set!_ne _ hi ‹_›, VG.Proof.MlKem.polyAt_get _ _ hi]

theorem reduced_writeW {m : Mem} {p : Addr} (hr : Reduced m p) {j : Nat} (hj : j < n) {v : BitVec 32}
    (hv : v.toNat < q) : Reduced (m.writeW (VG.Proof.MlKem.coeffAddr p j) v) p := fun i hi => by
  rw [VG.Proof.MlKem.coeffAt_writeW m p hi hj]
  split
  · exact hv
  · exact hr i hi

/-- The word stored for coefficient `i` of `f`. -/
theorem polyIs_toNat {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    (coeffAt m p i).toNat = (f[i]!).val := by
  rw [← h.2, VG.Proof.MlKem.polyAt_val h.1 hi]

theorem polyIs_coeffAt {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    coeffAt m p i = BitVec.ofNat 32 (f[i]!).val := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MlKem.polyIs_toNat h hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.MlKem.val_lt f[i]!; omega)]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAt m p i).toNat = (f[i]!).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, VG.Proof.MlKem.ext_getElem! fun i hi => ?_⟩
  rw [VG.Proof.MlKem.polyAt_get _ _ hi, h i hi, VG.Proof.MlKem.ofNat_val]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_coeffAt {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, coeffAt m p i = BitVec.ofNat 32 (f[i]!).val) : PolyIs m p f :=
  VG.Proof.MlKem.polyIs_of_toNat fun i hi => by
    rw [h i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.MlKem.val_lt f[i]!; omega)]

/-- Writing a coefficient of a stored polynomial. -/
theorem polyIs_writeW {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {j : Nat} (hj : j < n)
    (x : Zq) : PolyIs (m.writeW (VG.Proof.MlKem.coeffAddr p j) (BitVec.ofNat 32 x.val)) p (f.set! j x) := by
  have hx : (BitVec.ofNat 32 x.val).toNat = x.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.MlKem.val_lt x; omega)]
  refine ⟨VG.Proof.MlKem.reduced_writeW h.1 hj (by rw [hx]; exact x.isLt), ?_⟩
  rw [VG.Proof.MlKem.polyAt_writeW m p hj, hx, VG.Proof.MlKem.ofNat_val, h.2]

/-! ## Frames: the polynomial is unchanged by writes elsewhere -/

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  rw [VG.Proof.MlKem.n_eq] at hi
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem polyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    polyAt m' p = polyAt m p :=
  VG.Proof.MlKem.ext_getElem! fun i hi => by rw [VG.Proof.MlKem.polyAt_get _ _ hi, VG.Proof.MlKem.polyAt_get _ _ hi, VG.Proof.MlKem.coeffAt_congr h hi]

theorem reduced_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [VG.Proof.MlKem.coeffAt_congr h hi]; exact hr i hi

theorem polyIs_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p f := ⟨VG.Proof.MlKem.reduced_congr h hf.1, (VG.Proof.MlKem.polyAt_congr h).trans hf.2⟩

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) :
    ∀ k < len, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) :=
  fun _ hk => hf.bytes (R := ⟨p, len⟩) hd hlen hk

theorem polyAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.polyRegion p).Disjoint r) : polyAt m' p = polyAt m p :=
  VG.Proof.MlKem.polyAt_congr (VG.Proof.MlKem.bytes_frame hf hd (by decide))

theorem reduced_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.polyRegion p).Disjoint r) (hr : Reduced m p) : Reduced m' p :=
  VG.Proof.MlKem.reduced_congr (VG.Proof.MlKem.bytes_frame hf hd (by decide)) hr

theorem polyIs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.polyRegion p).Disjoint r) (h : PolyIs m p f) : PolyIs m' p f :=
  VG.Proof.MlKem.polyIs_congr (VG.Proof.MlKem.bytes_frame hf hd (by decide)) h

/-! ## Bytes -/

theorem bytesAt_length (m : Mem) (p : Addr) (len : Nat) : (bytesAt m p len).length = len := by
  simp [bytesAt]

theorem bytesAt_getElem (m : Mem) (p : Addr) {len i : Nat} (hi : i < (bytesAt m p len).length) :
    (bytesAt m p len)[i] = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

theorem bytesAt_getD (m : Mem) (p : Addr) {len i : Nat} (hi : i < len) :
    (bytesAt m p len).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [VG.Proof.MlKem.bytesAt_length]; exact hi),
    Option.getD_some, VG.Proof.MlKem.bytesAt_getElem]

theorem bytesAt_getElem! (m : Mem) (p : Addr) {len i : Nat} (hi : i < len) :
    (bytesAt m p len)[i]! = m (p + BitVec.ofNat 64 i) := by
  rw [getElem!_pos _ _ (by rw [VG.Proof.MlKem.bytesAt_length]; exact hi), VG.Proof.MlKem.bytesAt_getElem]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show m _ = m _
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k len : Nat} (h : k ≤ len) :
    (bytesAt m p len).take k = bytesAt m p k := by
  rw [show len = k + (len - k) by omega, VG.Proof.MlKem.bytesAt_add, List.take_left' (VG.Proof.MlKem.bytesAt_length _ _ _)]

theorem bytesAt_drop (m : Mem) (p : Addr) {k len : Nat} (h : k ≤ len) :
    (bytesAt m p len).drop k = bytesAt m (p + BitVec.ofNat 64 k) (len - k) := by
  rw [show len = k + (len - k) by omega, VG.Proof.MlKem.bytesAt_add, List.drop_left' (VG.Proof.MlKem.bytesAt_length _ _ _),
    Nat.add_sub_cancel_left]

/-- `(B.drop k).take c` of the bytes at `p`: the `c` bytes at `p + k`. -/
theorem bytesAt_slice (m : Mem) (p : Addr) {k c len : Nat} (h : k + c ≤ len) :
    ((bytesAt m p len).drop k).take c = bytesAt m (p + BitVec.ofNat 64 k) c := by
  rw [VG.Proof.MlKem.bytesAt_drop m p (by omega), VG.Proof.MlKem.bytesAt_take _ _ (by omega)]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {len : Nat}
    (h : ∀ i < len, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' p len = bytesAt m p len :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The bytes at `p` are `L` if each is. -/
theorem bytesAt_eq {m : Mem} {p : Addr} {L : List Byte} {len : Nat} (hl : L.length = len)
    (h : ∀ i (hi : i < len), m (p + BitVec.ofNat 64 i) = L[i]'(by omega)) : bytesAt m p len = L :=
  List.ext_getElem (by rw [VG.Proof.MlKem.bytesAt_length, hl]) fun i h₁ _ => by
    rw [VG.Proof.MlKem.bytesAt_getElem]; exact h i (by rw [VG.Proof.MlKem.bytesAt_length] at h₁; exact h₁)

/-- The bytes at `p` are `L` if each is (with `L[i]!`, as the lemmas of
`Encode.lean` state bytes). -/
theorem bytesAt_eq! {m : Mem} {p : Addr} {L : List Byte} {len : Nat} (hl : L.length = len)
    (h : ∀ i < len, m (p + BitVec.ofNat 64 i) = L[i]!) : bytesAt m p len = L :=
  VG.Proof.MlKem.bytesAt_eq hl fun i hi => by rw [h i hi, getElem!_pos L i (by omega)]

/-- The 34-byte input `ρ ‖ j ‖ i` of `SampleNTT`, from its pieces in memory. -/
theorem seed_eq {m : Mem} {p : Addr} {ρ : List Byte} (hρ : bytesAt m p 32 = ρ) {j i : Byte}
    (hj : m (p + BitVec.ofNat 64 32) = j) (hi : m (p + BitVec.ofNat 64 33) = i) :
    bytesAt m p 34 = ρ ++ [j, i] := by
  rw [show 34 = 32 + 2 from rfl, VG.Proof.MlKem.bytesAt_add, hρ]
  refine congrArg (ρ ++ ·) (VG.Proof.MlKem.bytesAt_eq rfl fun k hk => ?_)
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [BitVec.add_zero]; exact hj
  · rw [Offset.add_add]; exact hi

/-- The byte at `p`, from the one byte at `p`. -/
theorem mem_of_bytesAt_one {m : Mem} {p : Addr} {b : Byte} (h : bytesAt m p 1 = [b]) : m p = b := by
  rw [← BitVec.add_zero p]; exact List.head_eq_of_cons_eq h

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) :
    bytesAt m' p len = bytesAt m p len :=
  VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlKem.bytes_frame hf hd hlen)

export VG.WriteBytes (writeW8_apply)

/-- Writing byte `i` of the bytes at `p`. -/
theorem bytesAt_writeW8 (m : Mem) (p : Addr) {i len : Nat} (hi : i < len) (hlen : len ≤ 2 ^ 64)
    (b : Byte) : bytesAt (m.writeW (p + BitVec.ofNat 64 i) b) p len = (bytesAt m p len).set i b := by
  refine List.ext_getElem (by simp [VG.Proof.MlKem.bytesAt_length]) fun k h₁ h₂ => ?_
  rw [VG.Proof.MlKem.bytesAt_getElem, List.getElem_set, VG.Proof.MlKem.bytesAt_getElem, VG.WriteBytes.writeW8_apply]
  rw [VG.Proof.MlKem.bytesAt_length] at h₁
  by_cases hk : i = k
  · subst hk; simp
  · have : p + BitVec.ofNat 64 k ≠ p + BitVec.ofNat 64 i := by
      intro e
      apply hk
      bv_omega
    simp [this, hk]

/-- Writing a byte apart from the bytes at `p`. -/
theorem bytesAt_writeW_sep (m : Mem) (p : Addr) {len : Nat} {a : Addr} {w : Nat} (v : BitVec w)
    (h : Mem.Sep p len a (w / 8)) (hlen : len < 2 ^ 64) :
    bytesAt (m.writeW a v) p len = bytesAt m p len :=
  VG.Proof.MlKem.bytesAt_congr fun i hi => Mem.write_apply (h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hi))

end VG.Proof.MlKem

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Bits`. -/
section

/-!
# ML-KEM: bit arrays as numbers, for every target

`ByteEncode_d` and `ByteDecode_d` (Algorithms 5 and 6) go through arrays of
bits (`BitsToBytes`, `BytesToBits`, Algorithms 3 and 4). Here they are
restated without bits: a list of integers less than `2ʷ` is the digits of a
little-endian number in base `2ʷ` (`digits w`), and

* byte `k` of `ByteEncode_d(F)` is byte `k` of the number whose base-`2ᵈ`
  digits are `F` (`byteEncode_getElem`);
* `ByteDecode_d(B)[i]` is base-`2ᵈ` digit `i` of the number whose bytes are
  `B`, reduced modulo `m` (`byteDecode_getElem`);
* both group by group: `d · c = 8 · b` bits are `c` integers or `b` bytes
  (`byteEncode_group`, `byteDecode_group`), from which `Encode.lean`
  derives the formulas an implementation computes.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## Numbers from digits -/

/-- The little-endian number whose base-`2ʷ` digits are `L`:
`L[0] + 2ʷ · L[1] + 2²ʷ · L[2] + ⋯`. -/
def digits (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: L => a + 2 ^ w * digits w L

theorem digits_nil (w : Nat) : digits w [] = 0 := rfl

theorem digits_cons (w a : Nat) (L : List Nat) : digits w (a :: L) = a + 2 ^ w * digits w L := rfl

/-- `(a + 2ʷ · D) / 2ʷ = D` for a digit `a < 2ʷ`. -/
theorem add_pow_mul_div {w a : Nat} (ha : a < 2 ^ w) (D : Nat) : (a + 2 ^ w * D) / 2 ^ w = D := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem digits_lt {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → digits w L < 2 ^ (w * L.length)
  | [], _ => by simp [digits]
  | a :: L, h => by
    have ha := h a (List.mem_cons_self ..)
    have hL := digits_lt (L := L) fun b hb => h b (List.mem_cons_of_mem _ hb)
    have h1 : 2 ^ w * digits w L + 2 ^ w ≤ 2 ^ w * 2 ^ (w * L.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hL
    rw [digits_cons, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * L.length))]
    omega

/-- The low `c` digits. -/
theorem digits_mod {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ c,
    digits w L % 2 ^ (w * c) = digits w (L.take c)
  | [], _, c => by simp [digits]
  | a :: L, h, 0 => by simp [Nat.mod_one, digits]
  | a :: L, h, c + 1 => by
    have ha := h a (List.mem_cons_self ..)
    rw [List.take_succ_cons, digits_cons, digits_cons, Nat.mul_succ, Nat.pow_add,
      Nat.mul_comm (2 ^ (w * c)), Nat.mod_mul, add_pow_mul_div ha,
      digits_mod (fun b hb => h b (List.mem_cons_of_mem _ hb)) c, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha]

/-- The digits from `s` on. -/
theorem digits_div {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ s,
    digits w L / 2 ^ (w * s) = digits w (L.drop s)
  | L, _, 0 => by simp
  | [], _, s + 1 => by simp [digits]
  | a :: L, h, s + 1 => by
    have ha := h a (List.mem_cons_self ..)
    rw [List.drop_succ_cons, digits_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * s)),
      ← Nat.div_div_eq_div_mul, add_pow_mul_div ha,
      digits_div (fun b hb => h b (List.mem_cons_of_mem _ hb)) s]

/-- Digits `s … s + c - 1`. -/
theorem digits_chunk {w : Nat} {L : List Nat} (h : ∀ a ∈ L, a < 2 ^ w) (s c : Nat) :
    digits w L / 2 ^ (w * s) % 2 ^ (w * c) = digits w ((L.drop s).take c) := by
  rw [digits_div h, digits_mod (fun a ha => h a (List.mem_of_mem_drop ha))]

/-- Bit `p` of the number is bit `p mod w` of digit `⌊p / w⌋`. -/
theorem digits_bit {w : Nat} (hw : 0 < w) : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ p,
    digits w L / 2 ^ p % 2 = L.getD (p / w) 0 / 2 ^ (p % w) % 2
  | [], _, p => by simp [digits]
  | a :: L, h, p => by
    have ha := h a (List.mem_cons_self ..)
    rw [digits_cons]
    by_cases hp : p < w
    · rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, List.getD_cons_zero]
      have e : 2 ^ w = 2 ^ p * 2 ^ (w - p) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos p)]
      have e2 : 2 ^ (w - p) = 2 * 2 ^ (w - p - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [e2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · have e : 2 ^ p = 2 ^ w * 2 ^ (p - w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, ← Nat.div_div_eq_div_mul, add_pow_mul_div ha,
        digits_bit hw (fun b hb => h b (List.mem_cons_of_mem _ hb)) (p - w),
        show p / w = (p - w) / w + 1 from Nat.div_eq_sub_div hw (by omega), List.getD_cons_succ,
        show p % w = (p - w) % w from Nat.mod_eq_sub_mod (by omega)]

/-- Bits `p … p + n - 1` of the number whose base-`2ʷ` digits are `L`, digit
by digit (`digits_window`): a function of literals that `simp only [win]`
evaluates to the digits involved, so that a field or byte of the number is
an expression in two or three digits rather than in all of them. -/
def win (w : Nat) : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | a :: L, p, n =>
    if w ≤ p then win w L (p - w) n
    else if n < w - p then a / 2 ^ p % 2 ^ n
    else a / 2 ^ p + 2 ^ (w - p) * win w L 0 (n - (w - p))

theorem digits_window {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ p n,
    digits w L / 2 ^ p % 2 ^ n = win w L p n
  | [], _, p, n => by simp [digits, win]
  | a :: L, h, p, n => by
    have ha := h a (List.mem_cons_self ..)
    have hL : ∀ b ∈ L, b < 2 ^ w := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [digits_cons, win]
    by_cases hp : w ≤ p
    · simp only [hp, ↓reduceIte]
      rw [show p = w + (p - w) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
        add_pow_mul_div ha, Nat.add_sub_cancel_left, digits_window hL]
    · simp only [hp, ↓reduceIte]
      have e : 2 ^ w = 2 ^ p * 2 ^ (w - p) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos p)]
      by_cases hn : n < w - p
      · simp only [hn, ↓reduceIte]
        have e' : 2 ^ (w - p) = 2 ^ n * 2 ^ (w - p - n) := by rw [← Nat.pow_add]; congr 1; omega
        rw [e', Nat.mul_assoc, Nat.add_mul_mod_self_left]
      · simp only [hn, ↓reduceIte]
        have hlt : a / 2 ^ p < 2 ^ (w - p) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos p), Nat.mul_comm, ← e]; exact ha
        have e' : 2 ^ n = 2 ^ (w - p) * 2 ^ (n - (w - p)) := by rw [← Nat.pow_add]; congr 1; omega
        have := digits_window hL 0 (n - (w - p))
        rw [Nat.pow_zero, Nat.div_one] at this
        rw [e', Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
          add_pow_mul_div hlt, this]

/-- The sum of the bits `j < w` of `M`, each times `2ʲ`, is `M mod 2ʷ`. -/
theorem sum_bits (M : Nat) : ∀ w, ((List.range w).map fun j => M / 2 ^ j % 2 * 2 ^ j).sum = M % 2 ^ w
  | 0 => by simp [Nat.mod_one]
  | w + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_bits M w, Nat.mod_pow_succ]
    simp [Nat.mul_comm]

/-- `(X mod 2ᵃ) / 2ᵇ mod 2ᶜ = X / 2ᵇ mod 2ᶜ` when `b + c ≤ a`. -/
theorem mod_pow_div_mod (X : Nat) {a b c : Nat} (h : b + c ≤ a) :
    X % 2 ^ a / 2 ^ b % 2 ^ c = X / 2 ^ b % 2 ^ c := by
  rw [show a = b + (a - b) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- A byte is determined modulo 256. -/
theorem ofNat8_mod (x : Nat) : BitVec.ofNat 8 (x % 256) = BitVec.ofNat 8 x :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)

theorem ofNat8_eq {x y : Nat} (h : x % 256 = y % 256) : BitVec.ofNat 8 x = BitVec.ofNat 8 y := by
  rw [← ofNat8_mod x, h, ofNat8_mod]

/-! ## Lists of lists -/

theorem getElem?_flatMap_const {α β : Type} (f : α → List β) {d : Nat} (hd : 0 < d) :
    ∀ (L : List α), (∀ a ∈ L, (f a).length = d) → ∀ j,
      (L.flatMap f)[j]? = L[j / d]?.bind fun a => (f a)[j % d]?
  | [], _, j => by simp
  | a :: L, hf, j => by
    have ha := hf a (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    by_cases hj : j < d
    · rw [List.getElem?_append_left (by rw [ha]; exact hj), Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
      rfl
    · rw [List.getElem?_append_right (by rw [ha]; omega), ha,
        getElem?_flatMap_const f hd L (fun b hb => hf b (List.mem_cons_of_mem _ hb)) (j - d),
        show j / d = (j - d) / d + 1 from Nat.div_eq_sub_div hd (by omega),
        show j % d = (j - d) % d from Nat.mod_eq_sub_mod (by omega), List.getElem?_cons_succ]

theorem length_flatMap_const {α β : Type} (f : α → List β) {d : Nat} (hf : ∀ a, (f a).length = d) :
    ∀ L : List α, (L.flatMap f).length = d * L.length
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f hf L, List.length_cons,
      Nat.mul_succ, Nat.add_comm]

private theorem toNat_decide (x : Nat) : (decide (x % 2 = 1)).toNat = x % 2 := by
  cases Nat.mod_two_eq_zero_or_one x with
  | inl h => rw [h]; rfl
  | inr h => rw [h]; rfl

/-- Bit `p` of the concatenated bits of `L`: bit `p mod d` of `L[⌊p / d⌋]`,
as a number (0 past the end). -/
private theorem bits_getD {d : Nat} (hd : 0 < d) (L : List Nat) (p : Nat) :
    ((L.flatMap fun a => (List.range d).map fun j => decide (a / 2 ^ j % 2 = 1)).toArray.getD p
      false).toNat = L.getD (p / d) 0 / 2 ^ (p % d) % 2 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    getElem?_flatMap_const _ (d := d) hd _ (fun a _ => by simp), List.getD_eq_getElem?_getD]
  cases h : L[p / d]? with
  | none => simp
  | some a =>
    simp only [Option.bind_some, Option.getD_some,
      List.getElem?_map, List.getElem?_range (Nat.mod_lt _ hd), Option.map_some]
    exact toNat_decide _

/-- Bit `p` of `BytesToBits(B)`, as a number: bit `p mod 8` of byte
`⌊p / 8⌋` (0 past the end). -/
theorem bytesToBits_getD (B : List Byte) (p : Nat) :
    ((bytesToBits B).getD p false).toNat = (B.getD (p / 8) 0).toNat / 2 ^ (p % 8) % 2 := by
  simp only [bytesToBits]
  rw [show (B.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)) =
    (B.map (·.toNat)).flatMap (fun a => (List.range 8).map fun j => decide (a / 2 ^ j % 2 = 1)) by
      simp [List.flatMap_map], bits_getD (by decide) (B.map (·.toNat)) p]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases B[p / 8]? <;> rfl

/-! ## ByteEncode and ByteDecode -/

theorem byteEncode_length (d : Nat) (F : Vector Nat n) : (byteEncode d F).length = 32 * d := by
  simp only [byteEncode, bitsToBytes, List.length_map, List.length_range, List.size_toArray]
  rw [length_flatMap_const (d := d) _ (fun a => by simp) F.toList, Vector.length_toList, n_eq]
  omega

/-- Byte `k` of `ByteEncode_d(F)` is byte `k` of the number whose base-`2ᵈ`
digits are `F`. -/
theorem byteEncode_getElem {d : Nat} (hd : 0 < d) {F : Vector Nat n} (hF : ∀ a ∈ F.toList, a < 2 ^ d)
    {k : Nat} (hk : k < 32 * d) :
    (byteEncode d F)[k]! = BitVec.ofNat 8 (digits d F.toList / 2 ^ (8 * k)) := by
  rw [getElem!_pos _ _ (by rw [byteEncode_length]; exact hk)]
  simp only [byteEncode, bitsToBytes, List.getElem_map, List.getElem_range]
  rw [← ofNat8_mod (digits d F.toList / 2 ^ (8 * k))]
  refine congrArg (BitVec.ofNat 8) ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← sum_bits (digits d F.toList / 2 ^ (8 * k)) 8]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  rw [bits_getD hd F.toList (8 * k + j), ← digits_bit hd hF, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- Byte `b · g + j` of `ByteEncode_d(F)` when each group of `b` bytes holds
`c` integers (`d · c = 8 · b`): byte `j` of the number whose base-`2ᵈ`
digits are the `c` integers of group `g`. -/
theorem byteEncode_group {d c b : Nat} (hd : 0 < d) (hdc : d * c = 8 * b) {F : Vector Nat n}
    (hF : ∀ a ∈ F.toList, a < 2 ^ d) {g j : Nat} (hj : j < b) (hk : b * g + j < 32 * d) :
    (byteEncode d F)[b * g + j]! =
      BitVec.ofNat 8 (digits d ((F.toList.drop (c * g)).take c) / 2 ^ (8 * j)) := by
  have hx : 8 * (b * g + j) = d * (c * g) + 8 * j := by
    rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, hdc]
  rw [byteEncode_getElem hd hF hk, hx, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    ← ofNat8_mod (_ / 2 ^ (8 * j)), ← ofNat8_mod (digits d _ / 2 ^ (8 * j)), ← digits_chunk hF,
    show (256 : Nat) = 2 ^ 8 from rfl, mod_pow_div_mod _ (show 8 * j + 8 ≤ d * c by omega)]

theorem map_bytes_lt (B : List Byte) : ∀ a ∈ B.map (·.toNat), a < 2 ^ 8 := by
  intro a ha
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  exact x.isLt

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `ByteDecode_d(B)[i]` is base-`2ᵈ` digit `i` of the number whose bytes
are `B`, reduced modulo `m` (`2ᵈ`, or `q` for `d = 12`). -/
theorem byteDecode_getElem (d : Nat) (B : List Byte) {i : Nat} (hi : i < n) :
    (byteDecode d B)[i]! =
      digits 8 (B.map (·.toNat)) / 2 ^ (d * i) % 2 ^ d % (if d < 12 then 2 ^ d else q) := by
  rw [getElem!_pos (byteDecode d B) i hi]
  simp only [byteDecode, Vector.getElem_ofFn]
  refine congrArg (· % _) ?_
  rw [← sum_bits _ d]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  simp only [bytesToBits]
  rw [show (B.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)) =
    (B.map (·.toNat)).flatMap (fun a => (List.range 8).map fun j => decide (a / 2 ^ j % 2 = 1)) by
      simp [List.flatMap_map], bits_getD (by decide) (B.map (·.toNat)) (i * d + j),
    ← digits_bit (by decide) (map_bytes_lt B), Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_comm d i]

/-- `ByteDecode_d(B)[c · g + e]` when each group of `b` bytes holds `c`
integers (`d · c = 8 · b`): digit `e` of the number whose bytes are the `b`
bytes of group `g`. -/
theorem byteDecode_group {d c b : Nat} (hdc : d * c = 8 * b) (B : List Byte) {g e : Nat} (he : e < c)
    (hi : c * g + e < n) :
    (byteDecode d B)[c * g + e]! =
      digits 8 (((B.drop (b * g)).take b).map (·.toNat)) / 2 ^ (d * e) % 2 ^ d %
        (if d < 12 then 2 ^ d else q) := by
  have hx : d * (c * g + e) = 8 * (b * g) + d * e := by
    rw [Nat.mul_add, ← Nat.mul_assoc, hdc, Nat.mul_assoc]
  have hde : d * e + d ≤ 8 * b := by
    rw [← hdc, show d * e + d = d * (e + 1) by rw [Nat.mul_succ]]; exact Nat.mul_le_mul_left _ he
  rw [byteDecode_getElem d B hi, List.map_take, List.map_drop, ← digits_chunk (map_bytes_lt B),
    mod_pow_div_mod _ hde, Nat.div_div_eq_div_mul, ← Nat.pow_add, hx]

/-! ## Explicit groups -/

/-- `c` consecutive elements from `s`, when they are in the list. -/
theorem take_drop_eq {α : Type} (L : List α) (x : α) {s c : Nat} (h : s + c ≤ L.length) :
    (L.drop s).take c = (List.range c).map fun j => L.getD (s + j) x := by
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

/-- A list of `c · N` elements is the concatenation of `N` lists of `c`
elements if each element is. -/
theorem eq_flatMap {α : Type} [Inhabited α] {L : List α} {g : Nat → List α} {c N : Nat} (hc : 0 < c)
    (hg : ∀ i < N, (g i).length = c) (hL : L.length = c * N)
    (h : ∀ i < N, ∀ j < c, L[c * i + j]! = (g i)[j]!) : L = (List.range N).flatMap g := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_flatMap_const g hc _ fun i hi => hg i (List.mem_range.mp hi)]
  by_cases hk : k < c * N
  · have hq : k / c < N := Nat.div_lt_of_lt_mul hk
    have hr : k % c < c := Nat.mod_lt _ hc
    rw [List.getElem?_range hq, Option.bind_some, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by rw [hg _ hq]; exact hr)]
    have := h (k / c) hq (k % c) hr
    rw [Nat.div_add_mod, getElem!_pos L k (by omega),
      getElem!_pos (g (k / c)) _ (by rw [hg _ hq]; exact hr)] at this
    rw [this]
  · rw [List.getElem?_eq_none (by omega : L.length ≤ k),
      List.getElem?_eq_none (l := List.range N) (by
        rw [List.length_range]; exact (Nat.le_div_iff_mul_le hc).mpr (by rw [Nat.mul_comm]; omega)),
      Option.bind_none]

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Compress`. -/
section

/-!
# ML-KEM: Compress and Decompress without division, for every target

`Compress_d` (4.7) divides by `q`, and `Decompress_d` (4.8) by `2ᵈ`. For the
widths ML-KEM-768 uses (`compressWidths`: 1, 4 and 10), an implementation
computes them with a 32-bit multiply-low, an addition and shifts:

* `Compress_d(x) = ((x · M_d + 262080) >> 19) mod 2ᵈ` for every `x < q`,
  with `M₁ = 315`, `M₄ = 2520` and `M₁₀ = 161271` (`compressMul`); the
  intermediate value is less than `2³⁰` (`compress_eq`, `compress_arg_lt`);
* `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d` for every `y < 2ᵈ`, which is less
  than `q` (`decompress_val`).

The compress formula is checked for each of the `q` inputs by the kernel.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The multiplier `M_d` of the compress formula: 315, 2520 and 161271 for
`d` = 1, 4 and 10. -/
def compressMul (d : Nat) : Nat := if d = 1 then 315 else if d = 4 then 2520 else 161271

/-- The addend of the compress formula, `2¹⁸ - 64`. -/
def compressAdd : Nat := 262080

theorem mem_compressWidths {d : Nat} (hd : d ∈ compressWidths) : d = 1 ∨ d = 4 ∨ d = 10 := by
  simpa [compressWidths] using hd

/-- `p x` for every `x < n`, as a `Nat.rec` over `Nat.beq`, which the kernel
evaluates much faster than the `Decidable` instance of a bounded `∀`. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool := Nat.rec true (fun i ih => p i && ih) n

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) :
    ∀ x < n, p x = true := by
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro x hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
    · exact ih h.2 x hx
    · exact h.1

/-- The compress formula for width `d`, multiplier `m` and addend `a`, on
every `x < q`, from the kernel's check of each. -/
theorem compress_formula {d m a : Nat}
    (h : allBelow 3329 (fun x => Nat.beq (roundDiv (2 ^ d * x) 3329 % 2 ^ d)
      ((x * m + a) / 2 ^ 19 % 2 ^ d)) = true) (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ d * x) 3329 % 2 ^ d = (x * m + a) / 2 ^ 19 % 2 ^ d :=
  Nat.eq_of_beq_eq_true (allBelow_spec h x hx)

private theorem compress1 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 1 * x) 3329 % 2 ^ 1 = (x * 315 + 262080) / 2 ^ 19 % 2 ^ 1 :=
  compress_formula (by decide +kernel) x hx

private theorem compress4 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 4 * x) 3329 % 2 ^ 4 = (x * 2520 + 262080) / 2 ^ 19 % 2 ^ 4 :=
  compress_formula (by decide +kernel) x hx

private theorem compress10 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 10 * x) 3329 % 2 ^ 10 = (x * 161271 + 262080) / 2 ^ 19 % 2 ^ 10 :=
  compress_formula (by decide +kernel) x hx

/-- `Compress_d(x)` with a multiplication, an addition and a shift, for `d`
in `compressWidths`. -/
theorem compress_eq {d : Nat} (hd : d ∈ compressWidths) (x : Zq) :
    compress d x = (x.val * compressMul d + compressAdd) / 2 ^ 19 % 2 ^ d := by
  rcases mem_compressWidths hd with rfl | rfl | rfl
  · exact compress1 x.val x.isLt
  · exact compress4 x.val x.isLt
  · exact compress10 x.val x.isLt

/-- The value shifted in `compress_eq` fits in 30 bits. -/
theorem compress_arg_lt {d : Nat} (hd : d ∈ compressWidths) (x : Zq) :
    x.val * compressMul d + compressAdd < 2 ^ 30 := by
  have := val_lt x
  rcases mem_compressWidths hd with rfl | rfl | rfl
  · show x.val * 315 + 262080 < 2 ^ 30; omega
  · show x.val * 2520 + 262080 < 2 ^ 30; omega
  · show x.val * 161271 + 262080 < 2 ^ 30; omega

theorem compress_lt (d : Nat) (x : Zq) : compress d x < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

/-- `Decompress_d(y)` with a multiplication, an addition and a shift, for
`1 ≤ d ≤ 11` and `y < 2ᵈ`: the result is less than `q`. -/
theorem decompress_val_of_le {d : Nat} (hd : 0 < d) (hd' : d ≤ 11) {y : Nat} (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hP : 2 ^ e ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
  have h : roundDiv (q * y) (2 ^ (e + 1)) = (q * y + 2 ^ e) / 2 ^ (e + 1) ∧
      (q * y + 2 ^ e) / 2 ^ (e + 1) < q := by
    rw [Nat.pow_succ] at hy ⊢
    simp only [roundDiv, q_eq]
    generalize 2 ^ e = P at *
    refine ⟨?_, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    rw [show 2 * (3329 * y) + P * 2 = 2 * (3329 * y + P) by omega, Nat.mul_div_mul_left _ _ (by decide)]
  rw [Nat.add_sub_cancel, decompress, ofNat_of_lt (h.1 ▸ h.2), h.1]
  exact ⟨rfl, h.2⟩

/-- `Decompress_d(y)` with a multiplication, an addition and a shift, for
`d` in `compressWidths` and `y < 2ᵈ`: the result is less than `q`. -/
theorem decompress_val {d : Nat} (hd : d ∈ compressWidths) {y : Nat} (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q :=
  decompress_val_of_le (by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide)
    (by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide) hy

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Compress1024`. -/
section

/-!
# ML-KEM-1024: Compress and Decompress without division, for every target

The analog of `Compress.lean` for the widths only ML-KEM-1024 compresses to
(`Spec.MlKem1024.compressWidths`: `d_v = 5` and `d_u = 11`), with a 32-bit
multiply-low, an addition and shifts:

* `Compress_d(x) = ((x · M_d + 261888) >> 19) mod 2ᵈ` for every `x < q`,
  with `M₅ = 5040` and `M₁₁ = 322542` (`compressMul1024`); the intermediate
  value is less than `2³⁰` (`compress1024_eq`, `compress1024_arg_lt`). The
  shift is that of `Compress.lean`; the addend `2¹⁸ - 2⁸` (not its
  `2¹⁸ - 64`, which is too large for `d = 11`) serves both widths.
* `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d` for every `y < 2ᵈ`, which is less
  than `q` (`decompress1024_val`).

Both use `Compress.lean`'s kernel check (`compress_formula`) and decompress
formula (`decompress_val_of_le`).

The compress formula is checked for each of the `q` inputs by the kernel.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The multiplier `M_d` of the compress formula of ML-KEM-1024: 5040 and
322542 for `d` = 5 and 11. -/
def compressMul1024 (d : Nat) : Nat := if d = 5 then 5040 else 322542

/-- The addend of the compress formula of ML-KEM-1024, `2¹⁸ - 2⁸`. -/
def compressAdd1024 : Nat := 261888

theorem mem_compressWidths1024 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) :
    d = 5 ∨ d = 11 := by
  simpa [Spec.MlKem1024.compressWidths] using hd

private theorem compress5 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 5 * x) 3329 % 2 ^ 5 = (x * 5040 + 261888) / 2 ^ 19 % 2 ^ 5 :=
  compress_formula (by decide +kernel) x hx

private theorem compress11 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 11 * x) 3329 % 2 ^ 11 = (x * 322542 + 261888) / 2 ^ 19 % 2 ^ 11 :=
  compress_formula (by decide +kernel) x hx

/-- `Compress_d(x)` with a multiplication, an addition and a shift, for `d`
in ML-KEM-1024's `compressWidths`. -/
theorem compress1024_eq {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (x : Zq) :
    compress d x = (x.val * compressMul1024 d + compressAdd1024) / 2 ^ 19 % 2 ^ d := by
  rcases mem_compressWidths1024 hd with rfl | rfl
  · exact compress5 x.val x.isLt
  · exact compress11 x.val x.isLt

/-- The value shifted in `compress1024_eq` fits in 30 bits. -/
theorem compress1024_arg_lt {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (x : Zq) :
    x.val * compressMul1024 d + compressAdd1024 < 2 ^ 30 := by
  have := val_lt x
  rcases mem_compressWidths1024 hd with rfl | rfl
  · show x.val * 5040 + 261888 < 2 ^ 30; omega
  · show x.val * 322542 + 261888 < 2 ^ 30; omega

/-- For `d = 11` the shifted value is less than `2¹¹`, so the reduction
modulo `2¹¹` of `compress1024_eq` does nothing. -/
theorem compress11_eq (x : Zq) : compress 11 x = (x.val * 322542 + 261888) / 2 ^ 19 := by
  rw [compress1024_eq (d := 11) (by decide), Nat.mod_eq_of_lt (by
    have := val_lt x; show (x.val * 322542 + 261888) / 2 ^ 19 < 2 ^ 11; omega)]
  rfl

/-- `Decompress_d(y)` with a multiplication, an addition and a shift, for
`d` in ML-KEM-1024's `compressWidths` and `y < 2ᵈ`: the result is less than
`q`. -/
theorem decompress1024_val {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : Nat}
    (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q :=
  decompress_val_of_le (by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide)
    (by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide) hy

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Encode`. -/
section

/-!
# ML-KEM: encoding, decoding and sampling byte by byte, for every target

The functions of §4.2 on bytes, restated group by group as the arithmetic an
implementation does (with `Bits.lean`), for reduced inputs:

* `ByteEncode₁₂`: 2 coefficients `f₀, f₁` per 3 bytes,
  `[f₀ mod 256, ⌊f₀/256⌋ + 16(f₁ mod 16), ⌊f₁/16⌋]` (`encode12_eq`);
  `ByteDecode₁₂`: `B₀ + 256(B₁ mod 16)` and `⌊B₁/16⌋ + 16B₂`, reduced modulo `q`
  (`decode12_even`, `decode12_odd`);
* `ByteEncode_d ∘ Compress_d` for any `d`, group by group
  (`compressEncode_group`), and for `d` = 1 (8 coefficients per byte), 4 (2
  per byte) and 10 (4 per 5 bytes) (`compressEncode1`, `compressEncode4`,
  `compressEncode10_*`), and `Decompress_d ∘ ByteDecode_d`
  (`decodeDecompress_group`, `decodeDecompress1`, `…4_*`, `…10_*`);
* `SamplePolyCBD₂`: coefficient `i` from nibble `i` of `B`
  (`samplePolyCBD2_get`, `samplePolyCBD2_val`).

Byte `k` of a list `B` is written `B.getD k 0`, which `bytesAt_getD`
(`Mem.lean`) reads from memory.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## Lists of coefficients -/

theorem map_toList_length (f : Poly) (g : Zq → Nat) : (f.map g).toList.length = 256 := by simp

theorem map_toList_getD (f : Poly) (g : Zq → Nat) {i : Nat} (hi : i < 256) :
    (f.map g).toList.getD i 0 = g f[i]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hi), Option.getD_some,
    Vector.getElem_toList, Vector.getElem_map, getElem!_eq _ hi]

theorem map_toList_lt (f : Poly) {g : Zq → Nat} {d : Nat} (hg : ∀ x, g x < 2 ^ d) :
    ∀ a ∈ (f.map g).toList, a < 2 ^ d := by
  intro a ha
  rw [Vector.toList_map] at ha
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  exact hg x

theorem val_lt_4096 (x : Zq) : x.val < 2 ^ 12 := by have := val_lt x; omega

theorem bytes_map_take_drop (B : List Byte) {s c : Nat} (h : s + c ≤ B.length) :
    ((B.drop s).take c).map (·.toNat) = (List.range c).map fun j => (B.getD (s + j) 0).toNat := by
  rw [take_drop_eq B 0 h, List.map_map]; rfl

theorem range2 : List.range 2 = [0, 1] := rfl
theorem range3 : List.range 3 = [0, 1, 2] := rfl
theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl
theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem map_getD_lt (B : List Byte) (s c : Nat) :
    ∀ a ∈ (List.range c).map (fun i => (B.getD (s + i) 0).toNat), a < 2 ^ 8 :=
  List.forall_mem_map.2 fun _ _ => (B.getD _ 0).isLt

theorem map_compress_lt (f : Poly) (d s c : Nat) :
    ∀ a ∈ (List.range c).map (fun i => compress d f[s + i]!), a < 2 ^ d :=
  List.forall_mem_map.2 fun _ _ => compress_lt d _

/-- A byte of a number given by its digits, digit by digit (`win`). -/
theorem ofNat8_digits {w : Nat} {L : List Nat} (h : ∀ a ∈ L, a < 2 ^ w) (p : Nat) :
    BitVec.ofNat 8 (digits w L / 2 ^ p) = BitVec.ofNat 8 (win w L p 8) := by
  rw [← digits_window h]; exact (ofNat8_mod _).symm

/-- Evaluates `win` on a literal list of digits and literal positions, and
closes the goal, a byte or field of a group (`… = BitVec.ofNat 8 x` or
`… = decompress d x`), by `omega` on the few digits left: much smaller
problems than the number of the whole group. -/
macro "win_eval" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  simp only [win, Nat.reduceMul, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, ↓reduceIte,
    Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  try first
    | exact congrArg (BitVec.ofNat 8) (by omega)
    | exact congrArg (decompress _) (by omega)))

/-- The digits of an explicit list. -/
theorem digits_map_range {w c : Nat} (g : Nat → Nat) :
    digits w ((List.range (c + 1)).map g) = g 0 + 2 ^ w * digits w ((List.range c).map (g ∘ (· + 1))) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, digits_cons]

theorem byte_lt (b : Byte) : b.toNat < 256 := b.isLt

/-! ## ByteEncode₁₂ and ByteDecode₁₂ -/

theorem encode12_length (f : Poly) : (encode12 f).length = 384 := byteEncode_length 12 _

/-- The three bytes of group `i` of `ByteEncode₁₂(f)`, as bytes of
`f[2i] + 2¹² · f[2i + 1]`. -/
theorem encode12_group (f : Poly) {i j : Nat} (hi : i < 128) (hj : j < 3) :
    (encode12 f)[3 * i + j]! =
      BitVec.ofNat 8 (((f[2 * i]!).val + 4096 * (f[2 * i + 1]!).val) / 2 ^ (8 * j)) := by
  rw [encode12, byteEncode_group (d := 12) (c := 2) (b := 3) (by decide) (by decide) (map_toList_lt f val_lt_4096) hj
    (by omega), take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  simp only [range2, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    map_toList_getD f _ (show 2 * i < 256 by omega), map_toList_getD f _ (show 2 * i + 1 < 256 by omega)]
  rfl

theorem encode12_byte0 (f : Poly) {i : Nat} (hi : i < 128) :
    (encode12 f)[3 * i]! = BitVec.ofNat 8 ((f[2 * i]!).val % 256) := by
  have h := encode12_group f hi (j := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  clear h
  exact ofNat8_eq (by have := val_lt f[2 * i]!; have := val_lt f[2 * i + 1]!; omega)

theorem encode12_byte1 (f : Poly) {i : Nat} (hi : i < 128) :
    (encode12 f)[3 * i + 1]! =
      BitVec.ofNat 8 ((f[2 * i]!).val / 256 + 16 * ((f[2 * i + 1]!).val % 16)) := by
  rw [encode12_group f hi (by decide)]
  exact ofNat8_eq (by have := val_lt f[2 * i]!; have := val_lt f[2 * i + 1]!; omega)

theorem encode12_byte2 (f : Poly) {i : Nat} (hi : i < 128) :
    (encode12 f)[3 * i + 2]! = BitVec.ofNat 8 ((f[2 * i + 1]!).val / 16) := by
  rw [encode12_group f hi (by decide)]
  exact ofNat8_eq (by have := val_lt f[2 * i]!; have := val_lt f[2 * i + 1]!; omega)

/-- `ByteEncode₁₂(f)`, 3 bytes per pair of coefficients. -/
theorem encode12_eq (f : Poly) :
    encode12 f = (List.range 128).flatMap fun i =>
      [BitVec.ofNat 8 ((f[2 * i]!).val % 256),
        BitVec.ofNat 8 ((f[2 * i]!).val / 256 + 16 * ((f[2 * i + 1]!).val % 16)),
        BitVec.ofNat 8 ((f[2 * i + 1]!).val / 16)] := by
  refine eq_flatMap (c := 3) (N := 128) (by decide) (fun _ _ => rfl) (encode12_length f) fun i hi j hj => ?_
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · rw [Nat.add_zero, encode12_byte0 f hi]; rfl
  · rw [encode12_byte1 f hi]; rfl
  · rw [encode12_byte2 f hi]; rfl

theorem decode12_get (B : List Byte) {k : Nat} (hk : k < n) :
    (decode12 B)[k]! = ofNat ((byteDecode 12 B)[k]!) := by
  rw [getElem!_eq _ hk, getElem!_pos (byteDecode 12 B) k hk]
  simp only [decode12, Vector.getElem_map]

/-- The integer that coefficients `2i` and `2i + 1` of `ByteDecode₁₂` are
the 12-bit fields of. -/
private theorem decode12_group (B : List Byte) (hB : B.length = 384) {i e : Nat} (hi : i < 128)
    (he : e < 2) :
    (decode12 B)[2 * i + e]! = ofNat (((B.getD (3 * i) 0).toNat + 256 * (B.getD (3 * i + 1) 0).toNat +
      65536 * (B.getD (3 * i + 2) 0).toNat) / 2 ^ (12 * e) % 4096) := by
  rw [decode12_get B (by rw [n_eq]; omega), byteDecode_group (c := 2) (b := 3) (by decide) B he
    (by rw [n_eq]; omega), bytes_map_take_drop B (by omega)]
  simp only [range3, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.lt_irrefl, ↓reduceIte, ofNat_mod]
  refine congrArg ofNat (congrArg (· % 4096) (congrArg (· / 2 ^ (12 * e)) ?_))
  omega

/-- Coefficient `2i` of `ByteDecode₁₂(B)`: `B[3i] + 256 · (B[3i + 1] mod 16)`,
modulo `q`. -/
theorem decode12_even (B : List Byte) (hB : B.length = 384) {i : Nat} (hi : i < 128) :
    (decode12 B)[2 * i]! =
      ofNat ((B.getD (3 * i) 0).toNat + 256 * ((B.getD (3 * i + 1) 0).toNat % 16)) := by
  have h := decode12_group B hB hi (e := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  clear h
  refine congrArg ofNat ?_
  have := byte_lt (B.getD (3 * i) 0); have := byte_lt (B.getD (3 * i + 1) 0)
  have := byte_lt (B.getD (3 * i + 2) 0)
  omega

/-- Coefficient `2i + 1` of `ByteDecode₁₂(B)`: `⌊B[3i + 1] / 16⌋ + 16 · B[3i + 2]`,
modulo `q`. -/
theorem decode12_odd (B : List Byte) (hB : B.length = 384) {i : Nat} (hi : i < 128) :
    (decode12 B)[2 * i + 1]! =
      ofNat ((B.getD (3 * i + 1) 0).toNat / 16 + 16 * (B.getD (3 * i + 2) 0).toNat) := by
  rw [decode12_group B hB hi (by decide)]
  refine congrArg ofNat ?_
  have := byte_lt (B.getD (3 * i) 0); have := byte_lt (B.getD (3 * i + 1) 0)
  have := byte_lt (B.getD (3 * i + 2) 0)
  omega

/-! ## ByteEncode_d ∘ Compress_d -/

theorem compressEncode_length (d : Nat) (f : Poly) : (compressEncode d f).length = 32 * d :=
  byteEncode_length d _

/-- Byte `b·g + j` of `ByteEncode_d(Compress_d(f))`, when each group of `b`
bytes holds `c` coefficients (`d · c = 8 · b`): byte `j` of the number whose
base-`2ᵈ` digits are the compressed coefficients `c·g … c·g + c - 1`. -/
theorem compressEncode_group {d c b : Nat} (hd : 0 < d) (hdc : d * c = 8 * b) (f : Poly) {g j : Nat}
    (hg : c * g + c ≤ 256) (hj : j < b) :
    (compressEncode d f)[b * g + j]! =
      BitVec.ofNat 8 (digits d ((List.range c).map fun i => compress d f[c * g + i]!) / 2 ^ (8 * j)) := by
  have h₁ : d * (c * (g + 1)) ≤ d * 256 := Nat.mul_le_mul_left d (by rw [Nat.mul_succ]; exact hg)
  have h₂ : d * (c * (g + 1)) = 8 * (b * g + b) := by rw [← Nat.mul_assoc, hdc, Nat.mul_assoc, Nat.mul_succ]
  rw [compressEncode, byteEncode_group hd hdc (map_toList_lt f (compress_lt d)) hj (by omega),
    take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * j))) (List.map_congr_left fun i hi => ?_)
  exact map_toList_getD f _ (by have := List.mem_range.mp hi; omega)

/-- Byte `k` of `ByteEncode₁(Compress₁(f))`: the compressed coefficients
`8k … 8k + 7` as its bits. -/
theorem compressEncode1 (f : Poly) {k : Nat} (hk : k < 32) :
    (compressEncode 1 f)[k]! = BitVec.ofNat 8 (compress 1 f[8 * k]! + 2 * compress 1 f[8 * k + 1]! +
      4 * compress 1 f[8 * k + 2]! + 8 * compress 1 f[8 * k + 3]! + 16 * compress 1 f[8 * k + 4]! +
      32 * compress 1 f[8 * k + 5]! + 64 * compress 1 f[8 * k + 6]! +
      128 * compress 1 f[8 * k + 7]!) := by
  have h := compressEncode_group (d := 1) (c := 8) (b := 1) (g := k) (j := 0) (by decide) (by decide) f (by omega)
    (by decide)
  rw [show 1 * k + 0 = k by omega] at h
  rw [h]
  clear h
  simp only [range8, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  refine congrArg (BitVec.ofNat 8) ?_
  omega

/-- Byte `k` of `ByteEncode₄(Compress₄(f))`: compressed coefficients `2k`
and `2k + 1`. -/
theorem compressEncode4 (f : Poly) {k : Nat} (hk : k < 128) :
    (compressEncode 4 f)[k]! = BitVec.ofNat 8 (compress 4 f[2 * k]! + 16 * compress 4 f[2 * k + 1]!) := by
  have h := compressEncode_group (d := 4) (c := 2) (b := 1) (g := k) (j := 0) (by decide) (by decide) f (by omega)
    (by decide)
  rw [show 1 * k + 0 = k by omega] at h
  rw [h]
  clear h
  simp only [range2, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one]

section
variable (f : Poly) {g : Nat} (hg : g < 64)
include hg

theorem compressEncode10_0 :
    (compressEncode 10 f)[5 * g]! = BitVec.ofNat 8 (compress 10 f[4 * g]! % 256) := by
  have h := compressEncode_group (d := 10) (c := 4) (b := 5) (g := g) (j := 0) (by decide) (by decide) f (by omega) (by decide)
  rw [Nat.add_zero] at h
  rw [h, ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range4, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode10_1 :
    (compressEncode 10 f)[5 * g + 1]! =
      BitVec.ofNat 8 (compress 10 f[4 * g]! / 256 + 4 * (compress 10 f[4 * g + 1]! % 64)) := by
  rw [compressEncode_group (d := 10) (c := 4) (b := 5) (g := g) (j := 1) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range4, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode10_2 :
    (compressEncode 10 f)[5 * g + 2]! =
      BitVec.ofNat 8 (compress 10 f[4 * g + 1]! / 64 + 16 * (compress 10 f[4 * g + 2]! % 16)) := by
  rw [compressEncode_group (d := 10) (c := 4) (b := 5) (g := g) (j := 2) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range4, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode10_3 :
    (compressEncode 10 f)[5 * g + 3]! =
      BitVec.ofNat 8 (compress 10 f[4 * g + 2]! / 16 + 64 * (compress 10 f[4 * g + 3]! % 4)) := by
  rw [compressEncode_group (d := 10) (c := 4) (b := 5) (g := g) (j := 3) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range4, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode10_4 :
    (compressEncode 10 f)[5 * g + 4]! = BitVec.ofNat 8 (compress 10 f[4 * g + 3]! / 4) := by
  rw [compressEncode_group (d := 10) (c := 4) (b := 5) (g := g) (j := 4) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range4, List.map_cons, List.map_nil]
  win_eval

end

/-! ## Decompress_d ∘ ByteDecode_d -/

theorem decodeDecompress_get (d : Nat) (B : List Byte) {k : Nat} (hk : k < n) :
    (decodeDecompress d B)[k]! = decompress d ((byteDecode d B)[k]!) := by
  rw [getElem!_eq _ hk, getElem!_pos (byteDecode d B) k hk]
  simp only [decodeDecompress, Vector.getElem_map]

/-- Coefficient `c·g + e` of `Decompress_d(ByteDecode_d(B))`, when each group
of `b` bytes holds `c` coefficients (`d · c = 8 · b`): `d`-bit field `e` of
the number whose bytes are `B[b·g … b·g + b - 1]`, decompressed. -/
theorem decodeDecompress_group {d c b : Nat} (hd : d < 12) (hdc : d * c = 8 * b) (B : List Byte) {g e : Nat}
    (hB : b * g + b ≤ B.length) (he : e < c) (hi : c * g + e < n) :
    (decodeDecompress d B)[c * g + e]! =
      decompress d (digits 8 ((List.range b).map fun i => (B.getD (b * g + i) 0).toNat) / 2 ^ (d * e) % 2 ^ d) := by
  rw [decodeDecompress_get d B hi, byteDecode_group hdc B he hi, bytes_map_take_drop B hB]
  simp only [hd, ↓reduceIte, Nat.mod_mod]

/-- Coefficient `i` of `Decompress₁(ByteDecode₁(B))`: bit `i mod 8` of byte
`⌊i / 8⌋`, decompressed. -/
theorem decodeDecompress1 (B : List Byte) {i : Nat} (hi : i < n) :
    (decodeDecompress 1 B)[i]! = decompress 1 ((B.getD (i / 8) 0).toNat / 2 ^ (i % 8) % 2) := by
  rw [decodeDecompress_get 1 B hi, byteDecode_getElem 1 B hi]
  simp only [Nat.pow_one, Nat.one_mul, Nat.reduceLT, ↓reduceIte, Nat.mod_mod]
  rw [digits_bit (by decide) (map_bytes_lt B)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases B[i / 8]? <;> rfl

private theorem decodeDecompress4_group (B : List Byte) (hB : B.length = 128) {i e : Nat}
    (hi : i < 128) (he : e < 2) :
    (decodeDecompress 4 B)[2 * i + e]! = decompress 4 ((B.getD i 0).toNat / 2 ^ (4 * e) % 16) := by
  rw [decodeDecompress_group (c := 2) (b := 1) (by decide) (by decide) B (by omega) he (by rw [n_eq]; omega)]
  simp only [List.range_one, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.mul_zero, Nat.one_mul]

/-- Coefficient `2i` of `Decompress₄(ByteDecode₄(B))`: the low nibble of
`B[i]`, decompressed. -/
theorem decodeDecompress4_even (B : List Byte) (hB : B.length = 128) {i : Nat} (hi : i < 128) :
    (decodeDecompress 4 B)[2 * i]! = decompress 4 ((B.getD i 0).toNat % 16) := by
  have h := decodeDecompress4_group B hB hi (e := 0) (by decide)
  rw [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  exact h

/-- Coefficient `2i + 1` of `Decompress₄(ByteDecode₄(B))`: the high nibble
of `B[i]`, decompressed. -/
theorem decodeDecompress4_odd (B : List Byte) (hB : B.length = 128) {i : Nat} (hi : i < 128) :
    (decodeDecompress 4 B)[2 * i + 1]! = decompress 4 ((B.getD i 0).toNat / 16) := by
  rw [decodeDecompress4_group B hB hi (by decide)]
  refine congrArg (decompress 4) ?_
  have := byte_lt (B.getD i 0)
  omega

section
variable (B : List Byte) (hB : B.length = 320) {g : Nat} (hg : g < 64)
include hB hg

/-- Coefficient `4g` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_0 :
    (decodeDecompress 10 B)[4 * g]! = decompress 10 ((B.getD (5 * g) 0).toNat +
      256 * ((B.getD (5 * g + 1) 0).toNat % 4)) := by
  have h := decodeDecompress_group (d := 10) (c := 4) (b := 5) (g := g) (e := 0) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega)
  rw [Nat.add_zero] at h
  rw [h, digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

/-- Coefficient `4g + 1` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_1 :
    (decodeDecompress 10 B)[4 * g + 1]! = decompress 10 ((B.getD (5 * g + 1) 0).toNat / 4 +
      64 * ((B.getD (5 * g + 2) 0).toNat % 16)) := by
  rw [decodeDecompress_group (d := 10) (c := 4) (b := 5) (g := g) (e := 1) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

/-- Coefficient `4g + 2` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_2 :
    (decodeDecompress 10 B)[4 * g + 2]! = decompress 10 ((B.getD (5 * g + 2) 0).toNat / 16 +
      16 * ((B.getD (5 * g + 3) 0).toNat % 64)) := by
  rw [decodeDecompress_group (d := 10) (c := 4) (b := 5) (g := g) (e := 2) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

/-- Coefficient `4g + 3` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_3 :
    (decodeDecompress 10 B)[4 * g + 3]! = decompress 10 ((B.getD (5 * g + 3) 0).toNat / 64 +
      4 * (B.getD (5 * g + 4) 0).toNat) := by
  rw [decodeDecompress_group (d := 10) (c := 4) (b := 5) (g := g) (e := 3) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

end

/-! ## SamplePolyCBD₂ -/

/-- `x` of `SamplePolyCBD₂` from the nibble `v`: its bits 0 and 1. -/
def cbdX (v : Nat) : Nat := v % 2 + v / 2 % 2

/-- `y` of `SamplePolyCBD₂` from the nibble `v`: its bits 2 and 3. -/
def cbdY (v : Nat) : Nat := v / 4 % 2 + v / 8 % 2

/-- Nibble `i` of `B` (the low nibble of byte `⌊i/2⌋` for even `i`, the high
one for odd `i`), shifted down: its low 4 bits are the nibble. -/
def nibble (B : List Byte) (i : Nat) : Nat := (B.getD (i / 2) 0).toNat / 16 ^ (i % 2)

private theorem cbd_bit (B : List Byte) (i j : Nat) (hj : j < 4) :
    ((bytesToBits B).getD (2 * i * 2 + j) false).toNat = nibble B i / 2 ^ j % 2 := by
  rw [bytesToBits_getD, nibble, show (2 * i * 2 + j) / 8 = i / 2 by omega,
    show (2 * i * 2 + j) % 8 = 4 * (i % 2) + j by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.pow_mul]

/-- Coefficient `i` of `SamplePolyCBD₂(B)`: `x - y` for the bits `x` and `y`
of nibble `i`. -/
theorem samplePolyCBD2_get (B : List Byte) {i : Nat} (hi : i < n) :
    (samplePolyCBD 2 B)[i]! = ofNat (cbdX (nibble B i)) - ofNat (cbdY (nibble B i)) := by
  rw [getElem!_eq _ hi]
  simp only [samplePolyCBD, Vector.getElem_ofFn, range2, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have h0 := cbd_bit B i 0 (by decide)
  rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
  rw [h0, cbd_bit B i 1 (by decide), show 2 * i * 2 + 2 + 1 = 2 * i * 2 + 3 by omega,
    cbd_bit B i 2 (by decide), cbd_bit B i 3 (by decide)]
  simp only [cbdX, cbdY, Nat.reducePow]

theorem cbdX_le (v : Nat) : cbdX v ≤ 2 := by unfold cbdX; omega

theorem cbdY_le (v : Nat) : cbdY v ≤ 2 := by unfold cbdY; omega

/-- Coefficient `i` of `SamplePolyCBD₂(B)`, as an integer: `x + q - y`,
reduced. -/
theorem samplePolyCBD2_val (B : List Byte) {i : Nat} (hi : i < n) :
    ((samplePolyCBD 2 B)[i]!).val = (cbdX (nibble B i) + q - cbdY (nibble B i)) % q := by
  have := cbdX_le (nibble B i); have := cbdY_le (nibble B i)
  rw [samplePolyCBD2_get B hi, val_sub', ofNat_of_lt (by rw [q_eq]; omega),
    ofNat_of_lt (by rw [q_eq]; omega), Nat.add_sub_assoc (by rw [q_eq]; omega)]

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.EkCheck`. -/
section

/-!
# ML-KEM: the encapsulation key check, for every target

The modulus check of §7.2, `ByteEncode₁₂(ByteDecode₁₂(ek[0 : 384k])) = ek[0 :
384k]`, holds exactly when both 12-bit fields of every 3-byte group of `ek[0 :
384k]` are less than `q` (`encode12_decode12`, `ekCheck_iff`, for any parameter set,
and `ekCheck768`, `ekCheck1024`): what a constant-time implementation checks,
without encoding anything.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The first 12-bit field of the 3-byte group `g` of `B`:
`B[3g] + 256 · (B[3g + 1] mod 16)`. -/
def field0 (B : List Byte) (g : Nat) : Nat :=
  (B.getD (3 * g) 0).toNat + 256 * ((B.getD (3 * g + 1) 0).toNat % 16)

/-- The second 12-bit field of the 3-byte group `g` of `B`:
`⌊B[3g + 1] / 16⌋ + 16 · B[3g + 2]`. -/
def field1 (B : List Byte) (g : Nat) : Nat :=
  (B.getD (3 * g + 1) 0).toNat / 16 + 16 * (B.getD (3 * g + 2) 0).toNat

/-! ## Lists -/

theorem flatMap_range_inj {α : Type} {g₁ g₂ : Nat → List α} {c N : Nat} (hc : 0 < c)
    (h₁ : ∀ i < N, (g₁ i).length = c) (h₂ : ∀ i < N, (g₂ i).length = c) :
    (List.range N).flatMap g₁ = (List.range N).flatMap g₂ ↔ ∀ i < N, g₁ i = g₂ i := by
  constructor
  · intro h i hi
    refine List.ext_getElem? fun j => ?_
    by_cases hj : j < c
    · have := congrArg (·[c * i + j]?) h
      simp only [getElem?_flatMap_const _ hc _ fun a ha => h₁ a (List.mem_range.mp ha),
        getElem?_flatMap_const _ hc _ fun a ha => h₂ a (List.mem_range.mp ha),
        show (c * i + j) / c = i by rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hj, Nat.add_zero],
        show (c * i + j) % c = j by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj],
        List.getElem?_range hi, Option.bind_some] at this
      exact this
    · rw [List.getElem?_eq_none (by rw [h₁ i hi]; omega), List.getElem?_eq_none (by rw [h₂ i hi]; omega)]
  · intro h
    simp only [List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun i hi => h i (List.mem_range.mp hi))

theorem getD_take_of_lt {α : Type} (L : List α) {x : α} {c j : Nat} (hj : j < c) :
    (L.take c).getD j x = L.getD j x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

theorem slice_getD {α : Type} (L : List α) (x : α) {s c j : Nat} (hj : j < c) :
    ((L.drop s).take c).getD j x = L.getD (s + j) x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, List.getElem?_drop]

/-- A list is the concatenation of its groups of `c`. -/
theorem eq_flatMap_slices {α : Type} [Inhabited α] (L : List α) {c N : Nat} (hc : 0 < c)
    (hL : L.length = c * N) : L = (List.range N).flatMap fun i => (L.drop (c * i)).take c := by
  have hl : ∀ i < N, ((L.drop (c * i)).take c).length = c := fun i hi => by
    have : c * i + c ≤ c * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    simp only [List.length_take, List.length_drop, hL]
    omega
  refine eq_flatMap hc hl hL fun i hi j hj => ?_
  have : c * i + c ≤ c * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [getElem!_pos L _ (by omega), getElem!_pos _ _ (by rw [hl i hi]; exact hj), List.getElem_take,
    List.getElem_drop]

/-! ## One polynomial -/

theorem bytes3_eq (L : List Byte) (hL : L.length = 384) :
    L = (List.range 128).flatMap fun g => [L.getD (3 * g) 0, L.getD (3 * g + 1) 0, L.getD (3 * g + 2) 0] :=
  eq_flatMap (c := 3) (by decide) (fun _ _ => rfl) hL fun i hi j hj => by
    rw [getElem!_pos L _ (by omega)]
    have e : ∀ k (hk : k < L.length), L[k] = L.getD k 0 := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact e (3 * i) (by omega)
    · exact e (3 * i + 1) (by omega)
    · exact e (3 * i + 2) (by omega)

private theorem ofNat8_eq_iff (x : Nat) (b : Byte) : BitVec.ofNat 8 x = b ↔ x % 256 = b.toNat := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]

/-- The three bytes of two 12-bit fields determine them. -/
private theorem bytes3_inj {a b a' b' : Nat} (ha : a < 4096) (hb : b < 4096) (ha' : a' < 4096)
    (hb' : b' < 4096) :
    (a % 256 = a' % 256 ∧ (a / 256 + 16 * (b % 16)) % 256 = (a' / 256 + 16 * (b' % 16)) % 256 ∧
      b / 16 % 256 = b' / 16 % 256) ↔ (a = a' ∧ b = b') := by
  omega

/-- The encoding of the two fields reduced modulo `q` is the encoding of
the fields exactly when they are less than `q`. -/
private theorem group_ok {F₀ F₁ c₀ c₁ c₂ : Nat} (h₀ : F₀ < 4096) (h₁ : F₁ < 4096) (e₀ : c₀ = F₀ % 256)
    (e₁ : c₁ = (F₀ / 256 + 16 * (F₁ % 16)) % 256) (e₂ : c₂ = F₁ / 16 % 256) :
    (F₀ % 3329 % 256 = c₀ ∧ (F₀ % 3329 / 256 + 16 * (F₁ % 3329 % 16)) % 256 = c₁ ∧
      F₁ % 3329 / 16 % 256 = c₂) ↔ (F₀ < 3329 ∧ F₁ < 3329) := by
  subst e₀ e₁ e₂
  have := Nat.mod_lt F₀ (show 3329 > 0 by decide)
  have := Nat.mod_lt F₁ (show 3329 > 0 by decide)
  rw [bytes3_inj (by omega) (by omega) h₀ h₁, Nat.mod_eq_iff_lt (by decide),
    Nat.mod_eq_iff_lt (by decide)]

/-- `ByteEncode₁₂(ByteDecode₁₂(C)) = C` exactly when both 12-bit fields of
every 3-byte group of `C` are less than `q`. -/
theorem encode12_decode12 (C : List Byte) (hC : C.length = 384) :
    encode12 (decode12 C) = C ↔ ∀ g < 128, field0 C g < q ∧ field1 C g < q := by
  conv => lhs; rhs; rw [bytes3_eq C hC]
  rw [encode12_eq, flatMap_range_inj (c := 3) (by decide) (fun _ _ => rfl) (fun _ _ => rfl)]
  refine forall_congr' fun g => imp_congr_right fun hg => ?_
  rw [decode12_even C hC hg, decode12_odd C hC hg, val_ofNat, val_ofNat]
  simp only [List.cons.injEq, and_true, ofNat8_eq_iff, field0, field1, q_eq, Nat.mod_mod]
  have := byte_lt (C.getD (3 * g) 0); have := byte_lt (C.getD (3 * g + 1) 0)
  have := byte_lt (C.getD (3 * g + 2) 0)
  exact group_ok (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## The encapsulation key check -/

/-- The encapsulation key check (§7.2) of a key of `384k + 32` bytes: both
12-bit fields of each of the `128k` groups of 3 bytes of `ek[0 : 384k]` are
less than `q`. -/
theorem ekCheck_iff (p : Params) (ek : List Byte) (h : ek.length = p.ekLen) :
    ekCheck p ek = true ↔ ∀ g < 128 * p.k, field0 ek g < q ∧ field1 ek g < q := by
  have hE : (ek.take (384 * p.k)).length = 384 * p.k := by
    simp only [List.length_take, h, Params.ekLen]; omega
  have hs : ∀ i < p.k, (((ek.take (384 * p.k)).drop (384 * i)).take 384).length = 384 := fun i hi => by
    simp only [List.length_take, List.length_drop, hE]; omega
  simp only [ekCheck, h, Bool.and_eq_true, beq_iff_eq, decide_true, true_and]
  rw [encodeVec, decodeVec, List.flatMap_map]
  conv => lhs; rhs; rw [eq_flatMap_slices (ek.take (384 * p.k)) (c := 384) (N := p.k) (by decide) hE]
  rw [flatMap_range_inj (c := 384) (by decide) (fun _ _ => encode12_length _) hs]
  constructor
  · intro H g hg
    have := (encode12_decode12 _ (hs (g / 128) (by omega))).mp (H (g / 128) (by omega)) (g % 128)
      (by omega)
    simp only [field0, field1, slice_getD _ _ (show 3 * (g % 128) < 384 by omega),
      slice_getD _ _ (show 3 * (g % 128) + 1 < 384 by omega),
      slice_getD _ _ (show 3 * (g % 128) + 2 < 384 by omega)] at this
    simp only [field0, field1]
    rw [getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega)] at this
    rwa [show 384 * (g / 128) + 3 * (g % 128) = 3 * g by omega,
      show 384 * (g / 128) + (3 * (g % 128) + 1) = 3 * g + 1 by omega,
      show 384 * (g / 128) + (3 * (g % 128) + 2) = 3 * g + 2 by omega] at this
  · intro H i hi
    refine (encode12_decode12 _ (hs i hi)).mpr fun g hg => ?_
    have := H (128 * i + g) (by omega)
    simp only [field0, field1, slice_getD _ _ (show 3 * g < 384 by omega),
      slice_getD _ _ (show 3 * g + 1 < 384 by omega), slice_getD _ _ (show 3 * g + 2 < 384 by omega)]
    rw [getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega),
      show 384 * i + 3 * g = 3 * (128 * i + g) by omega,
      show 384 * i + (3 * g + 1) = 3 * (128 * i + g) + 1 by omega,
      show 384 * i + (3 * g + 2) = 3 * (128 * i + g) + 2 by omega]
    exact this

/-- The encapsulation key check of ML-KEM-768 (§7.2) of a key of 1184
bytes: both 12-bit fields of each of the 384 groups of 3 bytes of
`ek[0 : 1152]` are less than `q`. -/
theorem ekCheck768 (ek : List Byte) (h : ek.length = 1184) :
    ekCheck mlKem768 ek = true ↔ ∀ g < 384, field0 ek g < q ∧ field1 ek g < q :=
  ekCheck_iff mlKem768 ek h

/-- The encapsulation key check of ML-KEM-1024 (§7.2) of a key of 1568
bytes: both 12-bit fields of each of the 512 groups of 3 bytes of
`ek[0 : 1536]` are less than `q`. -/
theorem ekCheck1024 (ek : List Byte) (h : ek.length = 1568) :
    ekCheck mlKem1024 ek = true ↔ ∀ g < 512, field0 ek g < q ∧ field1 ek g < q :=
  ekCheck_iff mlKem1024 ek h

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Encode1024`. -/
section

/-!
# ML-KEM-1024: compressed encodings byte by byte, for every target

The analog of the compressed encodings of `Encode.lean` for the widths only
ML-KEM-1024 compresses to, group by group as the arithmetic an implementation
does (with `Bits.lean`):

* `ByteEncode₅ ∘ Compress₅`: 8 coefficients per 5 bytes
  (`compressEncode5_group`, the 40-bit number of the group, and
  `compressEncode5_0` … `_4`, byte by byte), and `Decompress₅ ∘ ByteDecode₅`
  (`decodeDecompress5_group` and `decodeDecompress5_0` … `_7`, field by
  field);
* `ByteEncode₁₁ ∘ Compress₁₁`: 8 coefficients per 11 bytes
  (`compressEncode11_group`, `compressEncode11_0` … `_10`), and
  `Decompress₁₁ ∘ ByteDecode₁₁` (`decodeDecompress11_group`,
  `decodeDecompress11_0` … `_7`).

Byte `k` of a list `B` is written `B.getD k 0`, which `bytesAt_getD`
(`Mem.lean`) reads from memory, and byte `k` of an encoding `L[k]!`, which
`bytesAt_eq!` takes.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

theorem range11 : List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := rfl

/-! ## ByteEncode₅ ∘ Compress₅ -/

/-- Byte `5g + j` of `ByteEncode₅(Compress₅(f))`: byte `j` of the 40-bit
number of the compressed coefficients `8g … 8g + 7`. -/
theorem compressEncode5_group (f : Poly) {g j : Nat} (hg : g < 32) (hj : j < 5) :
    (compressEncode 5 f)[5 * g + j]! = BitVec.ofNat 8 ((compress 5 f[8 * g]! +
      32 * compress 5 f[8 * g + 1]! + 1024 * compress 5 f[8 * g + 2]! +
      32768 * compress 5 f[8 * g + 3]! + 1048576 * compress 5 f[8 * g + 4]! +
      33554432 * compress 5 f[8 * g + 5]! + 1073741824 * compress 5 f[8 * g + 6]! +
      34359738368 * compress 5 f[8 * g + 7]!) / 2 ^ (8 * j)) := by
  rw [compressEncode_group (c := 8) (by decide) (by decide) f (by omega) hj]
  simp only [range8, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  refine congrArg (BitVec.ofNat 8) (congrArg (· / 2 ^ (8 * j)) ?_)
  omega

section
variable (f : Poly) {g : Nat} (hg : g < 32)
include hg

theorem compressEncode5_0 :
    (compressEncode 5 f)[5 * g]! =
      BitVec.ofNat 8 (compress 5 f[8 * g]! + 32 * (compress 5 f[8 * g + 1]! % 8)) := by
  have h := compressEncode_group (d := 5) (c := 8) (b := 5) (g := g) (j := 0) (by decide) (by decide) f (by omega) (by decide)
  rw [Nat.add_zero] at h
  rw [h, ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode5_1 :
    (compressEncode 5 f)[5 * g + 1]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 1]! / 8 + 4 * compress 5 f[8 * g + 2]! +
        128 * (compress 5 f[8 * g + 3]! % 2)) := by
  rw [compressEncode_group (d := 5) (c := 8) (b := 5) (g := g) (j := 1) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode5_2 :
    (compressEncode 5 f)[5 * g + 2]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 3]! / 2 + 16 * (compress 5 f[8 * g + 4]! % 16)) := by
  rw [compressEncode_group (d := 5) (c := 8) (b := 5) (g := g) (j := 2) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode5_3 :
    (compressEncode 5 f)[5 * g + 3]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 4]! / 16 + 2 * compress 5 f[8 * g + 5]! +
        64 * (compress 5 f[8 * g + 6]! % 4)) := by
  rw [compressEncode_group (d := 5) (c := 8) (b := 5) (g := g) (j := 3) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode5_4 :
    (compressEncode 5 f)[5 * g + 4]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 6]! / 4 + 8 * compress 5 f[8 * g + 7]!) := by
  rw [compressEncode_group (d := 5) (c := 8) (b := 5) (g := g) (j := 4) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

end

/-! ## ByteEncode₁₁ ∘ Compress₁₁ -/

/-- Byte `11g + j` of `ByteEncode₁₁(Compress₁₁(f))`: byte `j` of the 88-bit
number of the compressed coefficients `8g … 8g + 7`. -/
theorem compressEncode11_group (f : Poly) {g j : Nat} (hg : g < 32) (hj : j < 11) :
    (compressEncode 11 f)[11 * g + j]! = BitVec.ofNat 8 ((compress 11 f[8 * g]! +
      2048 * compress 11 f[8 * g + 1]! + 4194304 * compress 11 f[8 * g + 2]! +
      8589934592 * compress 11 f[8 * g + 3]! + 17592186044416 * compress 11 f[8 * g + 4]! +
      36028797018963968 * compress 11 f[8 * g + 5]! +
      73786976294838206464 * compress 11 f[8 * g + 6]! +
      151115727451828646838272 * compress 11 f[8 * g + 7]!) / 2 ^ (8 * j)) := by
  rw [compressEncode_group (c := 8) (by decide) (by decide) f (by omega) hj]
  simp only [range8, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  refine congrArg (BitVec.ofNat 8) (congrArg (· / 2 ^ (8 * j)) ?_)
  omega

section
variable (f : Poly) {g : Nat} (hg : g < 32)
include hg

theorem compressEncode11_0 :
    (compressEncode 11 f)[11 * g]! = BitVec.ofNat 8 (compress 11 f[8 * g]! % 256) := by
  have h := compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 0) (by decide) (by decide) f (by omega) (by decide)
  rw [Nat.add_zero] at h
  rw [h, ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_1 :
    (compressEncode 11 f)[11 * g + 1]! =
      BitVec.ofNat 8 (compress 11 f[8 * g]! / 256 + 8 * (compress 11 f[8 * g + 1]! % 32)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 1) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_2 :
    (compressEncode 11 f)[11 * g + 2]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 1]! / 32 + 64 * (compress 11 f[8 * g + 2]! % 4)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 2) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_3 :
    (compressEncode 11 f)[11 * g + 3]! = BitVec.ofNat 8 (compress 11 f[8 * g + 2]! / 4 % 256) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 3) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_4 :
    (compressEncode 11 f)[11 * g + 4]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 2]! / 1024 + 2 * (compress 11 f[8 * g + 3]! % 128)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 4) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_5 :
    (compressEncode 11 f)[11 * g + 5]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 3]! / 128 + 16 * (compress 11 f[8 * g + 4]! % 16)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 5) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_6 :
    (compressEncode 11 f)[11 * g + 6]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 4]! / 16 + 128 * (compress 11 f[8 * g + 5]! % 2)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 6) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_7 :
    (compressEncode 11 f)[11 * g + 7]! = BitVec.ofNat 8 (compress 11 f[8 * g + 5]! / 2 % 256) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 7) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_8 :
    (compressEncode 11 f)[11 * g + 8]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 5]! / 512 + 4 * (compress 11 f[8 * g + 6]! % 64)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 8) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_9 :
    (compressEncode 11 f)[11 * g + 9]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 6]! / 64 + 32 * (compress 11 f[8 * g + 7]! % 8)) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 9) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

theorem compressEncode11_10 :
    (compressEncode 11 f)[11 * g + 10]! = BitVec.ofNat 8 (compress 11 f[8 * g + 7]! / 8) := by
  rw [compressEncode_group (d := 11) (c := 8) (b := 11) (g := g) (j := 10) (by decide) (by decide) f (by omega) (by decide),
    ofNat8_digits (map_compress_lt f _ _ _)]
  simp only [range8, List.map_cons, List.map_nil]
  win_eval

end

/-! ## Decompress₅ ∘ ByteDecode₅ -/

/-- Coefficient `8g + e` of `Decompress₅(ByteDecode₅(B))`: 5-bit field `e`
of the 40-bit number of bytes `5g … 5g + 4`. -/
theorem decodeDecompress5_group (B : List Byte) (hB : B.length = 160) {g e : Nat}
    (hg : g < 32) (he : e < 8) :
    (decodeDecompress 5 B)[8 * g + e]! = decompress 5 (((B.getD (5 * g) 0).toNat +
      256 * (B.getD (5 * g + 1) 0).toNat + 65536 * (B.getD (5 * g + 2) 0).toNat +
      16777216 * (B.getD (5 * g + 3) 0).toNat + 4294967296 * (B.getD (5 * g + 4) 0).toNat) /
        2 ^ (5 * e) % 32) := by
  rw [decodeDecompress_group (c := 8) (b := 5) (by decide) (by decide) B (by omega) he (by rw [n_eq]; omega)]
  simp only [range5, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  refine congrArg (decompress 5) (congrArg (· % 32) (congrArg (· / 2 ^ (5 * e)) ?_))
  omega

section
variable (B : List Byte) (hB : B.length = 160) {g : Nat} (hg : g < 32)
include hB hg

theorem decodeDecompress5_0 :
    (decodeDecompress 5 B)[8 * g]! = decompress 5 ((B.getD (5 * g) 0).toNat % 32) := by
  have h := decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 0) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega)
  rw [Nat.add_zero] at h
  rw [h, digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_1 :
    (decodeDecompress 5 B)[8 * g + 1]! = decompress 5 ((B.getD (5 * g) 0).toNat / 32 +
      8 * ((B.getD (5 * g + 1) 0).toNat % 4)) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 1) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_2 :
    (decodeDecompress 5 B)[8 * g + 2]! = decompress 5 ((B.getD (5 * g + 1) 0).toNat / 4 % 32) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 2) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_3 :
    (decodeDecompress 5 B)[8 * g + 3]! = decompress 5 ((B.getD (5 * g + 1) 0).toNat / 128 +
      2 * ((B.getD (5 * g + 2) 0).toNat % 16)) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 3) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_4 :
    (decodeDecompress 5 B)[8 * g + 4]! = decompress 5 ((B.getD (5 * g + 2) 0).toNat / 16 +
      16 * ((B.getD (5 * g + 3) 0).toNat % 2)) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 4) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_5 :
    (decodeDecompress 5 B)[8 * g + 5]! = decompress 5 ((B.getD (5 * g + 3) 0).toNat / 2 % 32) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 5) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_6 :
    (decodeDecompress 5 B)[8 * g + 6]! = decompress 5 ((B.getD (5 * g + 3) 0).toNat / 64 +
      4 * ((B.getD (5 * g + 4) 0).toNat % 8)) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 6) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress5_7 :
    (decodeDecompress 5 B)[8 * g + 7]! = decompress 5 ((B.getD (5 * g + 4) 0).toNat / 8) := by
  rw [decodeDecompress_group (d := 5) (c := 8) (b := 5) (g := g) (e := 7) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range5, List.map_cons, List.map_nil]
  win_eval

end

/-! ## Decompress₁₁ ∘ ByteDecode₁₁ -/

/-- The number whose base-256 digits are 11 bytes. -/
private theorem bytes11_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat) :
    b0 + 2 ^ 8 * (b1 + 2 ^ 8 * (b2 + 2 ^ 8 * (b3 + 2 ^ 8 * (b4 + 2 ^ 8 * (b5 + 2 ^ 8 * (b6 +
      2 ^ 8 * (b7 + 2 ^ 8 * (b8 + 2 ^ 8 * (b9 + 2 ^ 8 * (b10 + 2 ^ 8 * 0)))))))))) =
    b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 + 1099511627776 * b5 +
      281474976710656 * b6 + 72057594037927936 * b7 + 18446744073709551616 * b8 +
      4722366482869645213696 * b9 + 1208925819614629174706176 * b10 := by
  omega

/-- Coefficient `8g + e` of `Decompress₁₁(ByteDecode₁₁(B))`: 11-bit field
`e` of the 88-bit number of bytes `11g … 11g + 10`. -/
theorem decodeDecompress11_group (B : List Byte) (hB : B.length = 352) {g e : Nat}
    (hg : g < 32) (he : e < 8) :
    (decodeDecompress 11 B)[8 * g + e]! = decompress 11 (((B.getD (11 * g) 0).toNat +
      256 * (B.getD (11 * g + 1) 0).toNat + 65536 * (B.getD (11 * g + 2) 0).toNat +
      16777216 * (B.getD (11 * g + 3) 0).toNat + 4294967296 * (B.getD (11 * g + 4) 0).toNat +
      1099511627776 * (B.getD (11 * g + 5) 0).toNat +
      281474976710656 * (B.getD (11 * g + 6) 0).toNat +
      72057594037927936 * (B.getD (11 * g + 7) 0).toNat +
      18446744073709551616 * (B.getD (11 * g + 8) 0).toNat +
      4722366482869645213696 * (B.getD (11 * g + 9) 0).toNat +
      1208925819614629174706176 * (B.getD (11 * g + 10) 0).toNat) / 2 ^ (11 * e) % 2048) := by
  rw [decodeDecompress_group (c := 8) (b := 11) (by decide) (by decide) B (by omega) he (by rw [n_eq]; omega)]
  simp only [range11, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  exact congrArg (decompress 11) (congrArg (· % 2048) (congrArg (· / 2 ^ (11 * e)) (bytes11_eq ..)))

section
variable (B : List Byte) (hB : B.length = 352) {g : Nat} (hg : g < 32)
include hB hg

theorem decodeDecompress11_0 :
    (decodeDecompress 11 B)[8 * g]! = decompress 11 ((B.getD (11 * g) 0).toNat +
      256 * ((B.getD (11 * g + 1) 0).toNat % 8)) := by
  have h := decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 0) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega)
  rw [Nat.add_zero] at h
  rw [h, digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_1 :
    (decodeDecompress 11 B)[8 * g + 1]! = decompress 11 ((B.getD (11 * g + 1) 0).toNat / 8 +
      32 * ((B.getD (11 * g + 2) 0).toNat % 64)) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 1) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_2 :
    (decodeDecompress 11 B)[8 * g + 2]! = decompress 11 ((B.getD (11 * g + 2) 0).toNat / 64 +
      4 * (B.getD (11 * g + 3) 0).toNat + 1024 * ((B.getD (11 * g + 4) 0).toNat % 2)) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 2) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_3 :
    (decodeDecompress 11 B)[8 * g + 3]! = decompress 11 ((B.getD (11 * g + 4) 0).toNat / 2 +
      128 * ((B.getD (11 * g + 5) 0).toNat % 16)) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 3) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_4 :
    (decodeDecompress 11 B)[8 * g + 4]! = decompress 11 ((B.getD (11 * g + 5) 0).toNat / 16 +
      16 * ((B.getD (11 * g + 6) 0).toNat % 128)) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 4) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_5 :
    (decodeDecompress 11 B)[8 * g + 5]! = decompress 11 ((B.getD (11 * g + 6) 0).toNat / 128 +
      2 * (B.getD (11 * g + 7) 0).toNat + 512 * ((B.getD (11 * g + 8) 0).toNat % 4)) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 5) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_6 :
    (decodeDecompress 11 B)[8 * g + 6]! = decompress 11 ((B.getD (11 * g + 8) 0).toNat / 4 +
      64 * ((B.getD (11 * g + 9) 0).toNat % 32)) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 6) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

theorem decodeDecompress11_7 :
    (decodeDecompress 11 B)[8 * g + 7]! = decompress 11 ((B.getD (11 * g + 9) 0).toNat / 32 +
      8 * (B.getD (11 * g + 10) 0).toNat) := by
  rw [decodeDecompress_group (d := 11) (c := 8) (b := 11) (g := g) (e := 7) (by decide) (by decide) B (by omega) (by decide)
    (by rw [n_eq]; omega),
    digits_window (map_getD_lt B _ _)]
  simp only [range11, List.map_cons, List.map_nil]
  win_eval

end

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.KPke`. -/
section

section

section

/-!
# ML-KEM: the hash functions and XOFs through the streaming sponge

What a caller of `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze`
(`Spec/Sha3/Contract.lean`) needs to conclude that it computed `H`, `J`, `G`,
`PRF` or `XOF` (§4.1): from the all-zero state, which represents the empty
message (`repr_nil`), absorbing the pieces of the message, padding with the
suffix of the function (`sha3Suffix32`, `shakeSuffix32`), and squeezing from
position 0 gives the function (`H_eq`, `J_eq`, `G_eq`, `prf_eq`, `xof_eq`, as
`squeezeFrom` of the padded state `padded`); and output squeezed in pieces is
the concatenation (`squeezeFrom_append`). Byte `p` of the XOF output is the
same whatever the length asked for (`xof_getD`, `xofByte`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3
open VG.Proof.Sha3 (Rep rep_nil byteOf iterF length_squeezeFrom squeezeFrom_getElem length_squeeze
  squeeze_getElem)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`:
what `vg_keccak_pad` leaves (`padContract`). -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : State := absorb rate (pad rate suffix m)

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Repr mem p rate [] := by
  show stateAt mem p = Rep rate []
  rw [rep_nil, h]

/-- The `suffix` argument of `vg_keccak_pad` for SHA-3. -/
theorem sha3Suffix32 : (0x06 : BitVec 32).setWidth 8 = sha3Suffix := by decide

/-- The `suffix` argument of `vg_keccak_pad` for SHAKE. -/
theorem shakeSuffix32 : (0x1f : BitVec 32).setWidth 8 = shakeSuffix := by decide

theorem rate72 : 72 ∈ rates := by decide
theorem rate136 : 136 ∈ rates := by decide
theorem rate168 : 168 ∈ rates := by decide

/-- Output from position 0 is the output of `squeeze`. -/
theorem squeezeFrom_zero (rate : Nat) (S : State) (d : Nat) : squeezeFrom rate S 0 d = squeeze rate S d := by
  simp only [squeezeFrom, squeeze, Nat.zero_add, List.drop_zero]

/-- Output squeezed in two pieces. -/
theorem squeezeFrom_append {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (p a b : Nat) :
    squeezeFrom rate S p a ++ squeezeFrom rate S (p + a) b = squeezeFrom rate S p (a + b) := by
  refine List.ext_getElem (by rw [List.length_append, length_squeezeFrom hr hr', length_squeezeFrom hr hr',
    length_squeezeFrom hr hr']) fun i h₁ h₂ => ?_
  rw [length_squeezeFrom hr hr'] at h₂
  rw [squeezeFrom_getElem hr hr' _ h₂, List.getElem_append]
  split
  · rename_i h
    rw [length_squeezeFrom hr hr'] at h
    rw [squeezeFrom_getElem hr hr' _ h]
  · rename_i h
    rw [length_squeezeFrom hr hr'] at h
    rw [squeezeFrom_getElem hr hr' _ (by rw [length_squeezeFrom hr hr']; omega),
      show p + a + (i - (squeezeFrom rate S p a).length) = p + i by
        rw [length_squeezeFrom hr hr']; omega]

/-- Output from `p + a` of two states whose outputs from `p` and `c` agree. -/
theorem squeezeFrom_shift {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) {S P : State}
    {p c : Nat} (h : ∀ d, squeezeFrom rate S p d = squeezeFrom rate P c d) (a d : Nat) :
    squeezeFrom rate S (p + a) d = squeezeFrom rate P (c + a) d := by
  have e : ∀ (T : State) (x : Nat), squeezeFrom rate T (x + a) d = (squeezeFrom rate T x (a + d)).drop a :=
    fun T x => by rw [← squeezeFrom_append hr hr' T x a d, List.drop_left' (length_squeezeFrom hr hr' T x a)]
  rw [e S p, e P c, h]

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

/-! ## The functions of §4.1 -/

theorem sha3_256_eq (m : List Byte) : sha3_256 m = squeezeFrom 136 (padded 136 sha3Suffix m) 0 32 := by
  rw [squeezeFrom_zero]; rfl

theorem sha3_512_eq (m : List Byte) : sha3_512 m = squeezeFrom 72 (padded 72 sha3Suffix m) 0 64 := by
  rw [squeezeFrom_zero]; rfl

theorem shake128_eq (m : List Byte) (d : Nat) :
    shake128 m d = squeezeFrom 168 (padded 168 shakeSuffix m) 0 d := by
  rw [squeezeFrom_zero]; rfl

theorem shake256_eq (m : List Byte) (d : Nat) :
    shake256 m d = squeezeFrom 136 (padded 136 shakeSuffix m) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- `H(s) = SHA3-256(s)`: rate 136, suffix `0x06`, 32 bytes. -/
theorem H_eq (s : List Byte) : H s = squeezeFrom 136 (padded 136 sha3Suffix s) 0 32 := sha3_256_eq s

/-- `J(s) = SHAKE256(s, 256)`: rate 136, suffix `0x1f`, 32 bytes. -/
theorem J_eq (s : List Byte) : J s = squeezeFrom 136 (padded 136 shakeSuffix s) 0 32 := shake256_eq s 32

/-- `G(c) = SHA3-512(c)`, as its halves: rate 72, suffix `0x06`, 32 bytes
from position 0 and 32 bytes from position 32. -/
theorem G_eq (c : List Byte) :
    G c = (squeezeFrom 72 (padded 72 sha3Suffix c) 0 32, squeezeFrom 72 (padded 72 sha3Suffix c) 32 32) := by
  have e := squeezeFrom_append (rate := 72) (by decide) (by decide) (padded 72 sha3Suffix c) 0 32 32
  have hl := length_squeezeFrom (rate := 72) (by decide) (by decide) (padded 72 sha3Suffix c) 0 32
  simp only [G, sha3_512_eq, ← e, List.take_left' hl, List.drop_left' hl]

/-- `PRF_η(s, b) = SHAKE256(s ‖ b, 8 · 64η)`: rate 136, suffix `0x1f`,
`64η` bytes. -/
theorem prf_eq (η : Nat) (s : List Byte) (b : Byte) :
    prf η s b = squeezeFrom 136 (padded 136 shakeSuffix (s ++ [b])) 0 (64 * η) := shake256_eq _ _

/-- `XOF` (SHAKE128): rate 168, suffix `0x1f`. -/
theorem xof_eq (B : List Byte) (ℓ : Nat) : xof B ℓ = squeezeFrom 168 (padded 168 shakeSuffix B) 0 ℓ :=
  shake128_eq B ℓ

theorem H_length (s : List Byte) : (H s).length = 32 := length_squeeze (by decide) (by decide) _ _

theorem J_length (s : List Byte) : (J s).length = 32 := length_squeeze (by decide) (by decide) _ _

theorem G_fst_length (c : List Byte) : (G c).1.length = 32 := by
  simp only [G, List.length_take]
  rw [show (sha3_512 c).length = 64 from length_squeeze (by decide) (by decide) _ _]
  rfl

theorem G_snd_length (c : List Byte) : (G c).2.length = 32 := by
  simp only [G, List.length_drop]
  rw [show (sha3_512 c).length = 64 from length_squeeze (by decide) (by decide) _ _]

theorem prf_length (η : Nat) (s : List Byte) (b : Byte) : (prf η s b).length = 64 * η :=
  length_squeeze (by decide) (by decide) _ _

/-- Byte `p` of the output of `XOF` after absorbing `B`: byte `p mod 168`
of the padded state after `⌊p / 168⌋` more permutations. -/
def xofByte (B : List Byte) (p : Nat) : Byte :=
  byteOf (iterF (p / 168) (padded 168 shakeSuffix B)) (p % 168)

theorem xof_length (B : List Byte) (ℓ : Nat) : (xof B ℓ).length = ℓ :=
  length_squeeze (by decide) (by decide) _ _

theorem xof_getD (B : List Byte) {ℓ p : Nat} (hp : p < ℓ) : (xof B ℓ).getD p 0 = xofByte B p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [xof_length]; exact hp),
    Option.getD_some]
  exact squeeze_getElem (by decide) (by decide) _ hp

/-- Byte `i` of output squeezed from position `pos` of the XOF. -/
theorem xof_squeezeFrom_getElem (B : List Byte) {pos d i : Nat} (hi : i < d) :
    (squeezeFrom 168 (padded 168 shakeSuffix B) pos d)[i]'(by
      rw [length_squeezeFrom (by decide) (by decide)]; exact hi) = xofByte B (pos + i) :=
  squeezeFrom_getElem (by decide) (by decide) _ hi

end VG.Proof.MlKem

end

/-!
# ML-KEM: SampleNTT as a loop, and bounds on its iterations

`SampleNTT` (Algorithm 7) as the loop an implementation runs over the 3-byte
chunks of the XOF output (`xofByte`, above): `sampleAfter a out t` is the list
of coefficients accepted after the first `t` chunks, which stops growing once
it has 256 (`sampleStepCap`). An implementation that bounds the loop by
`iters` iterations and stops after `t ≤ iters` chunks with 256 coefficients
computes `sampleNTT iters B` (`sampleNTT_of_full`); one that reaches the bound
with fewer has `sampleNTT iters B = none` (`sampleNTT_none`).

A bigger bound gives the same result once the result is `some`
(`sampleNTT_mono`), and so do the algorithms built on `SampleNTT`
(`kpkeKeyGen_mono`, `kpkeEncrypt_mono`, `keyGenInternal_mono`,
`encapsInternal_mono`, `decapsInternal_mono`), and `Outcome` holds for an
implementation that bounds each `SampleNTT` by `minIterations`
(`outcome_of_min`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## One iteration -/

/-- Lines 5–15 of Algorithm 7 on the chunk `C = (c₀, c₁, c₂)`, from the
coefficients `a` sampled so far. -/
def sampleStep (a : List Zq) (c₀ c₁ c₂ : Byte) : List Zq :=
  let d₁ := c₀.toNat + 256 * (c₁.toNat % 16)
  let d₂ := c₁.toNat / 16 + 16 * c₂.toNat
  let a := if d₁ < q then a ++ [ofNat d₁] else a
  if d₂ < q ∧ a.length < n then a ++ [ofNat d₂] else a

/-- An iteration of the loop, which does nothing once there are 256
coefficients (the loop has ended). -/
def sampleStepCap (a : List Zq) (c₀ c₁ c₂ : Byte) : List Zq :=
  if a.length = n then a else sampleStep a c₀ c₁ c₂

/-- The coefficients sampled from `a` on after the first `t` chunks of the
bytes `out`, the loop stopping at 256 coefficients. -/
def sampleAfter (a : List Zq) (out : Nat → Byte) : Nat → List Zq
  | 0 => a
  | t + 1 => sampleStepCap (sampleAfter a out t) (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))

/-- The element of `T_q` whose coefficients are the first 256 of `a`. -/
def toPoly (a : List Zq) : Poly := Vector.ofFn fun i => a.getD i.val 0

theorem sampleAfter_zero (a : List Zq) (out : Nat → Byte) : sampleAfter a out 0 = a := rfl

theorem sampleAfter_succ (a : List Zq) (out : Nat → Byte) (t : Nat) :
    sampleAfter a out (t + 1) =
      sampleStepCap (sampleAfter a out t) (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2)) := rfl

theorem sampleStep_length (a : List Zq) (c₀ c₁ c₂ : Byte) (ha : a.length < n) :
    (sampleStep a c₀ c₁ c₂).length ≤ n := by
  simp only [sampleStep]
  split <;> split <;> simp_all <;> omega

theorem sampleStepCap_length {a : List Zq} (ha : a.length ≤ n) (c₀ c₁ c₂ : Byte) :
    (sampleStepCap a c₀ c₁ c₂).length ≤ n := by
  unfold sampleStepCap
  split
  · exact ha
  · exact sampleStep_length a c₀ c₁ c₂ (by omega)

theorem sampleStepCap_full {a : List Zq} (ha : a.length = n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a := by
  unfold sampleStepCap; rw [ite_eq_left ha]

/-- An iteration keeps the coefficients sampled before it. -/
theorem sampleStepCap_prefix (a : List Zq) (c₀ c₁ c₂ : Byte) : a <+: sampleStepCap a c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep
  split
  · exact List.prefix_refl a
  · dsimp only
    split <;> split
    all_goals first
      | exact List.prefix_refl a
      | exact List.prefix_append a _
      | exact (List.prefix_append a _).trans (List.prefix_append _ _)

theorem sampleAfter_length_le {a : List Zq} (ha : a.length ≤ n) (out : Nat → Byte) :
    ∀ t, (sampleAfter a out t).length ≤ n
  | 0 => ha
  | t + 1 => sampleStepCap_length (sampleAfter_length_le ha out t) _ _ _

/-- Once there are 256 coefficients, they stay. -/
theorem sampleAfter_full {a : List Zq} {out : Nat → Byte} {t : Nat} (h : (sampleAfter a out t).length = n) :
    ∀ t', t ≤ t' → sampleAfter a out t' = sampleAfter a out t := by
  intro t' ht
  have : ∀ k, sampleAfter a out (t + k) = sampleAfter a out t := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, sampleAfter_succ, ih, sampleStepCap_full h]
  rw [← this (t' - t), Nat.add_sub_cancel' ht]

/-- The coefficients sampled only depend on the bytes of the chunks read. -/
theorem sampleAfter_congr (a : List Zq) {out out' : Nat → Byte} :
    ∀ {t}, (∀ p < 3 * t, out p = out' p) → sampleAfter a out t = sampleAfter a out' t
  | 0, _ => rfl
  | t + 1, h => by
    rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_congr a fun p hp => h p (by omega),
      h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The first chunk, then the others. -/
theorem sampleAfter_succ' (a : List Zq) (out : Nat → Byte) :
    ∀ t, sampleAfter a out (t + 1) =
      sampleAfter (sampleStepCap a (out 0) (out 1) (out 2)) (fun p => out (p + 3)) t
  | 0 => rfl
  | t + 1 => by
    rw [sampleAfter_succ, sampleAfter_succ' a out t, sampleAfter_succ]
    congr 2 <;> congr 1 <;> omega

/-! ## The loop of the standard -/

/-- `sampleLoop` after it stops: the coefficients if there are 256. -/
private theorem sampleLoop_eq_after :
    ∀ (L : List Byte) (a : List Zq), a.length ≤ n →
      sampleLoop a L =
        if (sampleAfter a (fun p => L.getD p 0) (L.length / 3)).length = n
        then some (sampleAfter a (fun p => L.getD p 0) (L.length / 3)) else none
  | c₀ :: c₁ :: c₂ :: L, a, ha => by
    rw [sampleLoop]
    by_cases h : a.length = n
    · rw [ite_eq_left h, sampleAfter_full (t := 0) h _ (Nat.zero_le _), sampleAfter_zero, ite_eq_left h]
    · rw [ite_eq_right h]
      have hs : (c₀ :: c₁ :: c₂ :: L).length / 3 = L.length / 3 + 1 := by simp; omega
      have hf : (fun p => (c₀ :: c₁ :: c₂ :: L).getD (p + 3) 0) = fun p => L.getD p 0 := by
        funext p; simp only [List.getD_cons_succ]
      rw [hs, sampleAfter_succ', hf]
      simp only [List.getD_cons_zero, List.getD_cons_succ, sampleStepCap, ite_eq_right h]
      exact sampleLoop_eq_after L _ (sampleStep_length a c₀ c₁ c₂ (by omega))
  | [], a, _ => by
    rw [show ([] : List Byte).length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl
  | [x], a, _ => by
    rw [show [x].length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl
  | [x, y], a, _ => by
    rw [show [x, y].length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl

/-- `SampleNTT` with its loop bounded by `iters` iterations, as the
coefficients sampled after `iters` chunks of the XOF output. -/
theorem sampleNTT_eq (iters : Nat) (B : List Byte) :
    sampleNTT iters B =
      if (sampleAfter [] (xofByte B) iters).length = n
      then some (toPoly (sampleAfter [] (xofByte B) iters)) else none := by
  rw [sampleNTT, sampleLoop_eq_after _ [] (Nat.zero_le _), xof_length,
    show 3 * iters / 3 = iters by omega,
    sampleAfter_congr [] (out' := xofByte B) fun p hp => xof_getD B hp]
  split <;> rfl

/-- An implementation that has 256 coefficients after `t ≤ iters` chunks
computes `SampleNTT` bounded by `iters`. -/
theorem sampleNTT_of_full {iters t : Nat} {B : List Byte} (ht : t ≤ iters)
    (h : (sampleAfter [] (xofByte B) t).length = n) :
    sampleNTT iters B = some (toPoly (sampleAfter [] (xofByte B) t)) := by
  rw [sampleNTT_eq, sampleAfter_full h _ ht, ite_eq_left h]

/-- An implementation that has fewer than 256 coefficients after `iters`
chunks: `SampleNTT` bounded by `iters` fails. -/
theorem sampleNTT_none {iters : Nat} {B : List Byte} (h : (sampleAfter [] (xofByte B) iters).length ≠ n) :
    sampleNTT iters B = none := by
  rw [sampleNTT_eq, ite_eq_right h]

/-- A bigger bound on the iterations gives the same result. -/
theorem sampleNTT_mono {iters iters' : Nat} {B : List Byte} {a : Poly} (h : sampleNTT iters B = some a)
    (hi : iters ≤ iters') : sampleNTT iters' B = some a := by
  rw [sampleNTT_eq] at h
  split at h
  · rename_i hf
    rw [sampleNTT_of_full hi hf, h]
  · cases h

/-! ## The algorithms that sample -/

/-- `f` with a bound on the iterations of `SampleNTT` gives the same result
with any bigger bound, once it is `some`. -/
def Mono {α : Type} (f : Nat → Option α) : Prop :=
  ∀ ⦃iters iters' : Nat⦄ ⦃a : α⦄, f iters = some a → iters ≤ iters' → f iters' = some a

theorem Mono.bind {α β : Type} {f : Nat → Option α} (hf : Mono f) (g : α → Option β) :
    Mono fun iters => (f iters).bind g := by
  intro i i' b h hi
  dsimp only at h ⊢
  cases hx : f i with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; rw [hf hx hi]; exact h

theorem Mono.map {α β : Type} {f : Nat → Option α} (hf : Mono f) (g : α → β) :
    Mono fun iters => (f iters).map g := by
  intro i i' b h hi
  dsimp only at h ⊢
  cases hx : f i with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; rw [hf hx hi]; exact h

theorem mapM_mono {α β : Type} {f : α → Nat → Option β} (hf : ∀ x, Mono (f x)) :
    ∀ L : List α, Mono fun iters => L.mapM fun x => f x iters
  | [] => fun _ _ _ h _ => h
  | x :: L => by
    intro i i' b h hi
    simp only [List.mapM_cons] at h ⊢
    cases hx : f x i with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      cases hL : L.mapM (fun x => f x i) with
      | none => rw [hL] at h; cases h
      | some ys =>
        rw [hL] at h
        simp only [hf x hx hi, mapM_mono hf L hL hi]
        exact h

theorem sampleNTT_mono' (B : List Byte) : Mono fun iters => sampleNTT iters B :=
  fun _ _ _ h hi => sampleNTT_mono h hi

theorem sampleMatrix_mono (k : Nat) (ρ : List Byte) : Mono fun iters => sampleMatrix k iters ρ :=
  mapM_mono (fun _ => mapM_mono (fun _ => sampleNTT_mono' _) _) _

theorem kpkeKeyGen_mono (p : Params) (d : List Byte) : Mono fun iters => kpkeKeyGen p iters d := by
  simp only [kpkeKeyGen]
  exact (sampleMatrix_mono _ _).bind _

theorem kpkeEncrypt_mono (p : Params) (ek m r : List Byte) :
    Mono fun iters => kpkeEncrypt p iters ek m r := by
  simp only [kpkeEncrypt]
  exact (sampleMatrix_mono _ _).bind _

theorem keyGenInternal_mono (p : Params) (d z : List Byte) :
    Mono fun iters => keyGenInternal p iters d z := by
  simp only [keyGenInternal]
  exact (kpkeKeyGen_mono p d).bind _

theorem encapsInternal_mono (p : Params) (ek m : List Byte) :
    Mono fun iters => encapsInternal p iters ek m := by
  simp only [encapsInternal]
  exact (kpkeEncrypt_mono p ek m _).bind _

theorem decapsInternal_mono (p : Params) (dk c : List Byte) :
    Mono fun iters => decapsInternal p iters dk c := by
  simp only [decapsInternal]
  exact (kpkeEncrypt_mono p _ _ _).bind _

/-- The return value of an implementation that bounds each `SampleNTT` by
`minIterations` iterations: 1 if the algorithm so bounded succeeds, and 0
if not. -/
theorem outcome_of_min {α : Type} {f : Nat → Option α} {r : BitVec 32} {out : α}
    (h : (r = 1 ∧ f minIterations = some out) ∨ (r = 0 ∧ f minIterations = none)) :
    Outcome f r out := by
  rcases h with ⟨hr, hf⟩ | ⟨hr, hf⟩
  · exact .inl ⟨hr, minIterations, hf⟩
  · exact .inr ⟨hr, hf⟩

end VG.Proof.MlKem

end

/-!
# ML-KEM: K-PKE and the internal algorithms as polynomial steps

K-PKE.KeyGen, K-PKE.Encrypt, K-PKE.Decrypt (Algorithms 13–15) and the internal
algorithms (Algorithms 16–18) restated, for any parameter set `p` with
`η₁ = η₂ = 2` (ML-KEM-768 and ML-KEM-1024), as the sequence of calls of the
polynomial primitives (`Spec/MlKem/Poly.lean`) an implementation makes, so
that a proof of the top-level functions chains the primitives' contracts:

* `dotK a b k = (⋯(a₀ ×_T b₀ + a₁ ×_T b₁) + ⋯) + a_{k-1} ×_T b_{k-1}`,
  accumulated left to right with `add` (`dot_eq_dotK`), and `catK f k`
  the concatenation `f 0 ‖ ⋯ ‖ f (k - 1)`, both instances of `foldK`, which
  unfolds for a literal `k` to the explicit sum or concatenation;
* the matrix `Â` from the `k²` `SampleNTT`s (`sampleMatrix_some`,
  `sampleMatrix_none`);
* K-PKE.KeyGen: `t̂[i] = dotK (Â[i]) ŝ k + ê[i]`,
  `ek = ByteEncode₁₂(t̂[0]) ‖ … ‖ ρ`, `dk = ByteEncode₁₂(ŝ[0]) ‖ …`
  (`KPke.kpkeKeyGen_some`, `KPke.kpkeKeyGen_none`);
* K-PKE.Encrypt: `u[i] = NTT⁻¹(dotK (Â[·][i]) ŷ k) + e₁[i]`,
  `v = NTT⁻¹(dotK t̂ ŷ k) + e₂ + μ`, the ciphertext the compressed encodings
  of `u[0]`, …, `u[k-1]` and `v` (`KPke.kpkeEncrypt_some`,
  `KPke.kpkeEncrypt_none`);
* K-PKE.Decrypt (`KPke.kpkeDecrypt_eq`);
* the internal algorithms, and the layout of the decapsulation key
  (`KPke.keyGenInternal_eq`, `KPke.encapsInternal_eq`,
  `KPke.decapsInternal_eq`, `KPke.ekRho_dkEk`): decapsulation selects
  between `K'` and `K̄` by whether `c = c'`, which `eq_iff_foldl_or_xor`
  computes without branching.

The names of ML-KEM-768 (`kgRho`, `ekPKE768`, `kpkeKeyGen768_some`, …) and of
ML-KEM-1024 (`KPke1024.lean`) are these for `mlKem768` and `mlKem1024`.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## The matrix -/

theorem mapM_range_some {β : Type} {f : Nat → Option β} {a : Nat → β} :
    ∀ {k : Nat} (s : Nat), (∀ i < k, f (s + i) = some (a (s + i))) →
      (List.range' s k).mapM f = some ((List.range' s k).map a)
  | 0, _, _ => rfl
  | k + 1, s, h => by
    rw [List.range'_succ, List.mapM_cons, List.map_cons]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0, mapM_range_some (k := k) (s + 1) fun i hi => by
      rw [show s + 1 + i = s + (i + 1) by omega]; exact h (i + 1) (by omega)]
    rfl

theorem mapM_none {α β : Type} {f : α → Option β} : ∀ {L : List α} {x : α}, x ∈ L → f x = none →
    L.mapM f = none
  | y :: L, x, hx, h => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [h]; rfl
    · cases hy : f y with
      | none => rfl
      | some b => rw [mapM_none hx h]; rfl

/-- The seed `ρ ‖ j ‖ i` of `Â[i, j]`. -/
def matSeed (ρ : List Byte) (i j : Nat) : List Byte := ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i]

/-- The `k × k` matrix with entries `a i j`, as its rows. -/
def matrix (k : Nat) (a : Nat → Nat → Poly) : List (List Poly) :=
  (List.range k).map fun i => (List.range k).map fun j => a i j

theorem sampleMatrix_some {k iters : Nat} {ρ : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < k, ∀ j < k, sampleNTT iters (matSeed ρ i j) = some (a i j)) :
    sampleMatrix k iters ρ = some (matrix k a) := by
  rw [sampleMatrix, matrix, List.range_eq_range']
  refine mapM_range_some 0 fun i hi => ?_
  rw [Nat.zero_add]
  exact mapM_range_some 0 fun j hj => by rw [Nat.zero_add]; exact h i hi j hj

theorem sampleMatrix_none {k iters : Nat} {ρ : List Byte} {i j : Nat} (hi : i < k) (hj : j < k)
    (h : sampleNTT iters (matSeed ρ i j) = none) : sampleMatrix k iters ρ = none :=
  mapM_none (List.mem_range.mpr hi) (by
    cases hm : (List.range k).mapM (fun j => sampleNTT iters (ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i]))
    · rfl
    · rw [mapM_none (List.mem_range.mpr hj) h] at hm; cases hm)

/-- `SamplePolyCBD₂(PRF₂(s, N))`. -/
def cbd (s : List Byte) (N : Nat) : Poly := samplePolyCBD 2 (prf 2 s (BitVec.ofNat 8 N))

/-- `((L.take N).drop s).take c = (L.drop s).take c` when `s + c ≤ N`. -/
theorem slice_take {α : Type} (L : List α) {N s c : Nat} (h : s + c ≤ N) :
    ((L.take N).drop s).take c = (L.drop s).take c := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])`. -/
def ekT (ek : List Byte) (i : Nat) : Poly := decode12 ((ek.drop (384 * i)).take 384)

/-- `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))`. -/
def encY (r : List Byte) (j : Nat) : Poly := ntt (cbd r j)

/-- `ŝ[i] = ByteDecode₁₂(dk[384i : 384i + 384])`. -/
def dcS (dk : List Byte) (i : Nat) : Poly := decode12 ((dk.drop (384 * i)).take 384)


/-! ## Sums of products -/

namespace KPke

/-- `f 0 ⊕ f 1 ⊕ ⋯ ⊕ f (k - 1)` for `⊕ = op`, combined left to right from
`f 0`, and `z` for `k = 0`: for a literal `k`, it unfolds to the explicit
expression. -/
def foldK {α : Type} (op : α → α → α) (z : α) (f : Nat → α) : Nat → α
  | 0 => z
  | 1 => f 0
  | k + 2 => op (foldK op z f (k + 1)) (f (k + 1))

theorem foldK_succ {α : Type} {op : α → α → α} {z : α} (h : ∀ x, op z x = x) (f : Nat → α) :
    ∀ k, foldK op z f (k + 1) = op (foldK op z f k) (f k)
  | 0 => (h (f 0)).symm
  | _ + 1 => rfl

/-- `∑_{j<k} a j ×_{T_q} b j`, accumulated left to right with `add`. -/
abbrev dotK (a b : Nat → Poly) (k : Nat) : Poly := foldK add zero (fun j => multiplyNTTs (a j) (b j)) k

/-- `f 0 ‖ f 1 ‖ ⋯ ‖ f (k - 1)`. -/
abbrev catK (f : Nat → List Byte) (k : Nat) : List Byte := foldK (· ++ ·) [] f k

theorem dot_eq_dotK (a b : Nat → Poly) :
    ∀ k, dot ((List.range k).map a) ((List.range k).map b) = dotK a b k
  | 0 => rfl
  | k + 1 => by
    rw [dotK, foldK_succ zero_add_poly, ← dotK, ← dot_eq_dotK a b k]
    simp only [dot, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [List.zipWith_append (by simp), List.foldl_append]
    rfl

theorem catK_eq (f : Nat → List Byte) : ∀ k, catK f k = (List.range k).flatMap f
  | 0 => rfl
  | k + 1 => by
    rw [catK, foldK_succ List.nil_append, ← catK, catK_eq f k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

theorem catK_length {f : Nat → List Byte} {c : Nat} (hf : ∀ i, (f i).length = c) (k : Nat) :
    (catK f k).length = c * k := by
  rw [catK_eq, length_flatMap_const f hf, List.length_range]

/-! ## Vectors and matrices -/

theorem addVec_map {α : Type} (f g : α → Poly) :
    ∀ L : List α, addVec (L.map f) (L.map g) = L.map fun x => add (f x) (g x)
  | [] => rfl
  | x :: L => by simp only [addVec, List.map_cons, List.zipWith_cons_cons] at *; rw [← addVec, addVec_map f g L]

theorem mulMatVec_matrix (k : Nat) (a : Nat → Nat → Poly) (u : Nat → Poly) :
    mulMatVec (matrix k a) ((List.range k).map u) = (List.range k).map fun i => dotK (a i) u k := by
  simp only [mulMatVec, matrix, List.map_map]
  exact List.map_congr_left fun i _ => dot_eq_dotK (a i) u k

theorem mulMatTVec_matrix (k : Nat) (a : Nat → Nat → Poly) (u : Nat → Poly) :
    mulMatTVec k (matrix k a) ((List.range k).map u) =
      (List.range k).map fun i => dotK (fun j => a j i) u k := by
  refine List.map_congr_left fun i hi => ?_
  rw [← dot_eq_dotK]
  refine congrArg (dot · _) ?_
  simp only [matrix, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (List.mem_range.mp hi), Option.map_some, Option.getD_some]

/-- `k` samples `SamplePolyCBD₂(PRF₂(s, N₀ + i))`. -/
theorem sampleVec_two {η : Nat} (hη : η = 2) (k : Nat) (s : List Byte) (N₀ : Nat) :
    sampleVec k η s N₀ = (List.range k).map fun i => cbd s (N₀ + i) := by
  subst hη; rfl

theorem map_ntt_sampleVec {η : Nat} (hη : η = 2) (k : Nat) (s : List Byte) :
    (sampleVec k η s 0).map ntt = (List.range k).map fun j => ntt (cbd s j) := by
  rw [sampleVec_two hη, List.map_map]
  exact List.map_congr_left fun j _ => by rw [Function.comp, Nat.zero_add]

/-! ## K-PKE.KeyGen -/

variable (p : Params)

/-- `ρ` of K-PKE.KeyGen(d): the first half of `G(d ‖ k)`. -/
def kgRho (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 p.k])).1

/-- `σ` of K-PKE.KeyGen(d): the second half of `G(d ‖ k)`. -/
def kgSigma (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 p.k])).2

/-- `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`. -/
def kgS (d : List Byte) (j : Nat) : Poly := ntt (cbd (kgSigma p d) j)

/-- `ê[i] = NTT(SamplePolyCBD₂(PRF₂(σ, k + i)))`. -/
def kgE (d : List Byte) (i : Nat) : Poly := ntt (cbd (kgSigma p d) (p.k + i))

/-- `t̂[i] = Â[i] ∘ ŝ + ê[i]`. -/
def kgT (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := add (dotK (a i) (kgS p d) p.k) (kgE p d i)

/-- `ek_PKE = ByteEncode₁₂(t̂[0]) ‖ ⋯ ‖ ByteEncode₁₂(t̂[k - 1]) ‖ ρ`. -/
def ekPKE (a : Nat → Nat → Poly) (d : List Byte) : List Byte :=
  catK (fun i => encode12 (kgT p a d i)) p.k ++ kgRho p d

/-- `dk_PKE = ByteEncode₁₂(ŝ[0]) ‖ ⋯ ‖ ByteEncode₁₂(ŝ[k - 1])`. -/
def dkPKE (d : List Byte) : List Byte := catK (fun j => encode12 (kgS p d j)) p.k

theorem keyGenRho_eq (d : List Byte) : keyGenRho p d = kgRho p d := rfl

variable {p}

private theorem kpkeKeyGen_eq (iters : Nat) (d : List Byte) :
    kpkeKeyGen p iters d =
      (sampleMatrix p.k iters (kgRho p d)).bind fun A =>
        some (encodeVec (addVec (mulMatVec A ((sampleVec p.k p.η₁ (kgSigma p d) 0).map ntt))
          ((sampleVec p.k p.η₁ (kgSigma p d) p.k).map ntt)) ++ kgRho p d,
          encodeVec ((sampleVec p.k p.η₁ (kgSigma p d) 0).map ntt)) := by
  rfl

theorem kpkeKeyGen_some (hη : p.η₁ = 2) {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < p.k, ∀ j < p.k, sampleNTT iters (matSeed (kgRho p d) i j) = some (a i j)) :
    kpkeKeyGen p iters d = some (ekPKE p a d, dkPKE p d) := by
  rw [kpkeKeyGen_eq, sampleMatrix_some h, Option.bind_some, map_ntt_sampleVec hη, sampleVec_two hη,
    List.map_map, mulMatVec_matrix, addVec_map, encodeVec, encodeVec, List.flatMap_map, List.flatMap_map,
    ekPKE, dkPKE, catK_eq, catK_eq]
  rfl

theorem kpkeKeyGen_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < p.k) (hj : j < p.k)
    (h : sampleNTT iters (matSeed (kgRho p d) i j) = none) : kpkeKeyGen p iters d = none := by
  rw [kpkeKeyGen_eq, sampleMatrix_none hi hj h]; rfl

theorem ekPKE_length (a : Nat → Nat → Poly) (d : List Byte) : (ekPKE p a d).length = p.ekLen := by
  rw [ekPKE, List.length_append, catK_length fun _ => encode12_length _, kgRho, G_fst_length]; rfl

theorem dkPKE_length (d : List Byte) : (dkPKE p d).length = 384 * p.k :=
  catK_length (fun _ => encode12_length _) p.k

/-! ## K-PKE.Encrypt -/

variable (p)

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, with `e₁[i] = SamplePolyCBD₂(PRF₂(r, k + i))`. -/
def encU (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly :=
  add (nttInv (dotK (fun j => a j i) (encY r) p.k)) (cbd r (p.k + i))

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, with `e₂ = SamplePolyCBD₂(PRF₂(r, 2k))` and
`μ = Decompress₁(ByteDecode₁(m))`. -/
def encV (ek m r : List Byte) : Poly :=
  add (add (nttInv (dotK (ekT ek) (encY r) p.k)) (cbd r (2 * p.k))) (decodeDecompress 1 m)

/-- The ciphertext: `ByteEncode_{d_u}(Compress_{d_u}(u[i]))` for `i < k`, then
`ByteEncode_{d_v}(Compress_{d_v}(v))`. -/
def ct (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte :=
  catK (fun i => compressEncode p.du (encU p a r i)) p.k ++ compressEncode p.dv (encV p ek m r)

variable {p}

theorem ct_length (a : Nat → Nat → Poly) (ek m r : List Byte) : (ct p a ek m r).length = p.ctLen := by
  rw [ct, List.length_append, catK_length fun _ => compressEncode_length _ _, compressEncode_length,
    Params.ctLen, Nat.mul_add, Nat.mul_assoc]

private theorem kpkeEncrypt_eq (iters : Nat) (ek m r : List Byte) :
    kpkeEncrypt p iters ek m r =
      (sampleMatrix p.k iters (ekRho p ek)).bind fun A =>
        some ((addVec ((mulMatTVec p.k A ((sampleVec p.k p.η₁ r 0).map ntt)).map nttInv)
            (sampleVec p.k p.η₂ r p.k)).flatMap (compressEncode p.du) ++
          compressEncode p.dv (add (add (nttInv (dot (decodeVec p.k (ek.take (384 * p.k)))
            ((sampleVec p.k p.η₁ r 0).map ntt))) (samplePolyCBD p.η₂ (prf p.η₂ r (BitVec.ofNat 8 (2 * p.k)))))
            (decodeDecompress 1 m))) := by
  rfl

/-- `t̂ = ByteDecode₁₂(ek[384i : 384i + 384])` for `i < k`. -/
theorem decodeVec_take (k : Nat) (ek : List Byte) :
    decodeVec k (ek.take (384 * k)) = (List.range k).map (ekT ek) :=
  List.map_congr_left fun i hi => by
    rw [ekT, slice_take ek (show 384 * i + 384 ≤ 384 * k by have := List.mem_range.mp hi; omega)]

theorem kpkeEncrypt_some (hη : p.η₁ = 2 ∧ p.η₂ = 2) {iters : Nat} {ek m r : List Byte}
    {a : Nat → Nat → Poly} (h : ∀ i < p.k, ∀ j < p.k, sampleNTT iters (matSeed (ekRho p ek) i j) = some (a i j)) :
    kpkeEncrypt p iters ek m r = some (ct p a ek m r) := by
  rw [kpkeEncrypt_eq, sampleMatrix_some h, Option.bind_some, decodeVec_take, map_ntt_sampleVec hη.1,
    sampleVec_two hη.2, mulMatTVec_matrix, List.map_map, addVec_map, List.flatMap_map, dot_eq_dotK, hη.2,
    ct, catK_eq]
  rfl

theorem kpkeEncrypt_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < p.k) (hj : j < p.k)
    (h : sampleNTT iters (matSeed (ekRho p ek) i j) = none) :
    kpkeEncrypt p iters ek m r = none := by
  rw [kpkeEncrypt_eq, sampleMatrix_none hi hj h]; rfl

/-! ## K-PKE.Decrypt -/

variable (p)

/-- `u'[i] = Decompress_{d_u}(ByteDecode_{d_u}(c[32d_u·i : 32d_u·(i + 1)]))`. -/
def dcU (c : List Byte) (i : Nat) : Poly := decodeDecompress p.du ((c.drop (32 * p.du * i)).take (32 * p.du))

/-- `v' = Decompress_{d_v}(ByteDecode_{d_v}(c[32d_u·k : 32(d_u·k + d_v)]))`. -/
def dcV (c : List Byte) : Poly := decodeDecompress p.dv ((c.drop (32 * p.du * p.k)).take (32 * p.dv))

/-- K-PKE.Decrypt: `w = v' - NTT⁻¹(ŝ ∘ NTT(u'))`, and
`m = ByteEncode₁(Compress₁(w))`. -/
theorem kpkeDecrypt_eq (dk c : List Byte) :
    kpkeDecrypt p dk c =
      compressEncode 1 (VG.Spec.MlKem.sub (dcV p c) (nttInv (dotK (dcS dk) (fun i => ntt (dcU p c i)) p.k))) := by
  have e : kpkeDecrypt p dk c = compressEncode 1 (VG.Spec.MlKem.sub (dcV p c)
      (nttInv (dot ((List.range p.k).map (dcS dk)) ((List.range p.k).map fun i =>
        ntt (decodeDecompress p.du (((c.take (32 * p.du * p.k)).drop (32 * p.du * i)).take (32 * p.du))))))) := by
    simp only [kpkeDecrypt, List.map_map]; rfl
  rw [e, ← dot_eq_dotK]
  refine congrArg (fun L => compressEncode 1 (VG.Spec.MlKem.sub _ (nttInv (dot _ L)))) (List.map_congr_left fun i hi => ?_)
  rw [dcU, slice_take c (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (List.mem_range.mp hi))]

/-! ## The internal algorithms -/

/-- `ML-KEM.KeyGen_internal(d, z)`: `dk = dk_PKE ‖ ek ‖ H(ek) ‖ z`. -/
theorem keyGenInternal_eq (iters : Nat) (d z : List Byte) :
    keyGenInternal p iters d z = (kpkeKeyGen p iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) := by
  simp only [keyGenInternal]
  cases kpkeKeyGen p iters d <;> rfl

/-- `ML-KEM.Encaps_internal(ek, m)`: `(K, r) = G(m ‖ H(ek))`, and the
ciphertext of K-PKE.Encrypt with `r`. -/
theorem encapsInternal_eq (iters : Nat) (ek m : List Byte) :
    encapsInternal p iters ek m =
      (kpkeEncrypt p iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) := by
  simp only [encapsInternal]
  cases kpkeEncrypt p iters ek m (G (m ++ H ek)).2 <;> rfl

/-- `dk_PKE = dk[0 : 384k]`. -/
def dkPke (dk : List Byte) : List Byte := dk.take (384 * p.k)

/-- `ek_PKE = dk[384k : 768k + 32]`. -/
def dkEk (dk : List Byte) : List Byte := (dk.drop (384 * p.k)).take (384 * p.k + 32)

/-- `h = dk[768k + 32 : 768k + 64]`. -/
def dkH (dk : List Byte) : List Byte := (dk.drop (768 * p.k + 32)).take 32

/-- `z = dk[768k + 64 : 768k + 96]`. -/
def dkZ (dk : List Byte) : List Byte := (dk.drop (768 * p.k + 64)).take 32

/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
def decM (dk c : List Byte) : List Byte := kpkeDecrypt p (dkPke p dk) c

theorem decM_length (dk c : List Byte) : (decM p dk c).length = 32 := compressEncode_length 1 _

/-- `ρ` of the encapsulation key in `dk`. -/
theorem ekRho_dkEk (dk : List Byte) : ekRho p (dkEk p dk) = dkRho p dk := by
  simp only [ekRho, dkRho, dkEk, List.drop_take, List.drop_drop, List.take_take]
  rw [show 384 * p.k + 384 * p.k = 768 * p.k by omega, show 384 * p.k + 32 - 384 * p.k = 32 by omega,
    Nat.min_self]

/-- `ML-KEM.Decaps_internal(dk, c)`: `(K', r') = G(m' ‖ h)`, `c'` the
re-encryption of `m'` with `r'`, and the key `K'` if `c = c'`, and
`K̄ = J(z ‖ c)` otherwise. -/
theorem decapsInternal_eq (iters : Nat) (dk c : List Byte) :
    decapsInternal p iters dk c =
      (kpkeEncrypt p iters (dkEk p dk) (decM p dk c) (G (decM p dk c ++ dkH p dk)).2).map fun c' =>
        if c = c' then (G (decM p dk c ++ dkH p dk)).1 else J (dkZ p dk ++ c) := by
  show (kpkeEncrypt p iters (dkEk p dk) (decM p dk c) (G (decM p dk c ++ dkH p dk)).2).bind
      (fun c' => some (if c ≠ c' then J (dkZ p dk ++ c) else (G (decM p dk c ++ dkH p dk)).1)) = _
  cases kpkeEncrypt p iters (dkEk p dk) (decM p dk c) (G (decM p dk c ++ dkH p dk)).2 with
  | none => rfl
  | some c' =>
    rw [Option.bind_some, Option.map_some]
    by_cases h : c = c'
    · rw [ite_eq_right (fun h' : c ≠ c' => h' h), ite_eq_left h]
    · rw [ite_eq_left h, ite_eq_right h]

variable {p}

/-- The decapsulation key `dk_PKE ‖ ek ‖ H(ek) ‖ z` that key generation
writes, of `768k + 96` bytes for a 32-byte `z`. -/
theorem dk_length (a : Nat → Nat → Poly) (d z : List Byte) (hz : z.length = 32) :
    (dkPKE p d ++ ekPKE p a d ++ H (ekPKE p a d) ++ z).length = p.dkLen := by
  simp only [List.length_append, dkPKE_length, ekPKE_length, H_length, hz, Params.ekLen, Params.dkLen]
  omega

end KPke

/-- Two byte strings of the same length are equal exactly when the OR of
the XORs of their bytes is 0: the comparison of `c` and `c'` in constant
time. -/
theorem eq_iff_foldl_or_xor : ∀ {c c' : List Byte}, c.length = c'.length →
    (c = c' ↔ (List.zipWith (· ^^^ ·) c c').foldl (· ||| ·) 0 = 0) := by
  suffices h : ∀ {c c' : List Byte}, c.length = c'.length → ∀ acc : Byte,
      (List.zipWith (· ^^^ ·) c c').foldl (· ||| ·) acc = 0 ↔ acc = 0 ∧ c = c' by
    intro c c' hl
    rw [h hl 0]
    simp
  intro c
  induction c with
  | nil => intro c' hl acc; cases c' <;> simp_all
  | cons x c ih =>
    intro c' hl acc
    cases c' with
    | nil => simp at hl
    | cons y c' =>
      simp only [List.zipWith_cons_cons, List.foldl_cons, List.cons.injEq]
      rw [ih (by simpa using hl)]
      constructor
      · rintro ⟨h₁, h₂⟩
        obtain ⟨h₃, h₄⟩ := BitVec.or_eq_zero_iff.mp h₁
        exact ⟨h₃, BitVec.xor_eq_zero_iff.mp h₄, h₂⟩
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨BitVec.or_eq_zero_iff.mpr ⟨h₁, BitVec.xor_eq_zero_iff.mpr h₂⟩, h₃⟩

/-! ## ML-KEM-768

The names the proofs of each target use, for `mlKem768`. -/

/-- `∑_{j<3} a j ×_{T_q} b j`. -/
abbrev dot3 (a b : Nat → Poly) : Poly := KPke.dotK a b 3

abbrev kgRho (d : List Byte) : List Byte := KPke.kgRho mlKem768 d
abbrev kgSigma (d : List Byte) : List Byte := KPke.kgSigma mlKem768 d
abbrev kgS (d : List Byte) (j : Nat) : Poly := KPke.kgS mlKem768 d j
abbrev kgT (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := KPke.kgT mlKem768 a d i
abbrev ekPKE768 (a : Nat → Nat → Poly) (d : List Byte) : List Byte := KPke.ekPKE mlKem768 a d
abbrev dkPKE768 (d : List Byte) : List Byte := KPke.dkPKE mlKem768 d
abbrev encU (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly := KPke.encU mlKem768 a r i
abbrev encV (ek m r : List Byte) : Poly := KPke.encV mlKem768 ek m r
abbrev ct768 (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte := KPke.ct mlKem768 a ek m r
abbrev dcU (c : List Byte) (i : Nat) : Poly := KPke.dcU mlKem768 c i
abbrev dcV (c : List Byte) : Poly := KPke.dcV mlKem768 c
abbrev dkPke (dk : List Byte) : List Byte := KPke.dkPke mlKem768 dk
abbrev dkEk (dk : List Byte) : List Byte := KPke.dkEk mlKem768 dk
abbrev dkH (dk : List Byte) : List Byte := KPke.dkH mlKem768 dk
abbrev dkZ (dk : List Byte) : List Byte := KPke.dkZ mlKem768 dk
abbrev decM (dk c : List Byte) : List Byte := KPke.decM mlKem768 dk c

theorem kpkeKeyGen768_some {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 3, ∀ j < 3, sampleNTT iters (matSeed (kgRho d) i j) = some (a i j)) :
    kpkeKeyGen mlKem768 iters d = some (ekPKE768 a d, dkPKE768 d) :=
  KPke.kpkeKeyGen_some rfl h

theorem kpkeKeyGen768_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < 3) (hj : j < 3)
    (h : sampleNTT iters (matSeed (kgRho d) i j) = none) : kpkeKeyGen mlKem768 iters d = none :=
  KPke.kpkeKeyGen_none hi hj h

theorem kpkeEncrypt768_some {iters : Nat} {ek m r : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 3, ∀ j < 3, sampleNTT iters (matSeed (ekRho mlKem768 ek) i j) = some (a i j)) :
    kpkeEncrypt mlKem768 iters ek m r = some (ct768 a ek m r) :=
  KPke.kpkeEncrypt_some ⟨rfl, rfl⟩ h

theorem kpkeEncrypt768_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < 3) (hj : j < 3)
    (h : sampleNTT iters (matSeed (ekRho mlKem768 ek) i j) = none) :
    kpkeEncrypt mlKem768 iters ek m r = none :=
  KPke.kpkeEncrypt_none hi hj h

theorem kpkeDecrypt768 (dk c : List Byte) :
    kpkeDecrypt mlKem768 dk c =
      compressEncode 1 (VG.Spec.MlKem.sub (dcV c) (nttInv (dot3 (dcS dk) fun i => ntt (dcU c i)))) :=
  KPke.kpkeDecrypt_eq mlKem768 dk c

theorem keyGenInternal768 (iters : Nat) (d z : List Byte) :
    keyGenInternal mlKem768 iters d z =
      (kpkeKeyGen mlKem768 iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) :=
  KPke.keyGenInternal_eq mlKem768 iters d z

theorem encapsInternal768 (iters : Nat) (ek m : List Byte) :
    encapsInternal mlKem768 iters ek m =
      (kpkeEncrypt mlKem768 iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) :=
  KPke.encapsInternal_eq mlKem768 iters ek m

theorem decapsInternal768 (iters : Nat) (dk c : List Byte) :
    decapsInternal mlKem768 iters dk c =
      (kpkeEncrypt mlKem768 iters (dkEk dk) (decM dk c) (G (decM dk c ++ dkH dk)).2).map fun c' =>
        if c = c' then (G (decM dk c ++ dkH dk)).1 else J (dkZ dk ++ c) :=
  KPke.decapsInternal_eq mlKem768 iters dk c

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.KPke1024`. -/
section

/-!
# ML-KEM-1024: K-PKE and the internal algorithms as polynomial steps

The names the proofs of each target use for ML-KEM-1024 (`k = 4`,
`η₁ = η₂ = 2`, `d_u = 11`, `d_v = 5`): those of `KPke.lean`, which states
K-PKE and the internal algorithms for any parameter set, for `mlKem1024`.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- `∑_{j<4} a j ×_{T_q} b j`. -/
abbrev dot4 (a b : Nat → Poly) : Poly := KPke.dotK a b 4

abbrev kgRho1024 (d : List Byte) : List Byte := KPke.kgRho mlKem1024 d
abbrev kgSigma1024 (d : List Byte) : List Byte := KPke.kgSigma mlKem1024 d
abbrev kgS1024 (d : List Byte) (j : Nat) : Poly := KPke.kgS mlKem1024 d j
abbrev kgT1024 (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := KPke.kgT mlKem1024 a d i
abbrev ekPKE1024 (a : Nat → Nat → Poly) (d : List Byte) : List Byte := KPke.ekPKE mlKem1024 a d
abbrev dkPKE1024 (d : List Byte) : List Byte := KPke.dkPKE mlKem1024 d
abbrev encU1024 (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly := KPke.encU mlKem1024 a r i
abbrev encV1024 (ek m r : List Byte) : Poly := KPke.encV mlKem1024 ek m r
abbrev ct1024 (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte := KPke.ct mlKem1024 a ek m r
abbrev dcU1024 (c : List Byte) (i : Nat) : Poly := KPke.dcU mlKem1024 c i
abbrev dcV1024 (c : List Byte) : Poly := KPke.dcV mlKem1024 c
abbrev dkPke1024 (dk : List Byte) : List Byte := KPke.dkPke mlKem1024 dk
abbrev dkEk1024 (dk : List Byte) : List Byte := KPke.dkEk mlKem1024 dk
abbrev dkH1024 (dk : List Byte) : List Byte := KPke.dkH mlKem1024 dk
abbrev dkZ1024 (dk : List Byte) : List Byte := KPke.dkZ mlKem1024 dk
abbrev decM1024 (dk c : List Byte) : List Byte := KPke.decM mlKem1024 dk c

theorem kpkeKeyGen1024_some {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (kgRho1024 d) i j) = some (a i j)) :
    kpkeKeyGen mlKem1024 iters d = some (ekPKE1024 a d, dkPKE1024 d) :=
  KPke.kpkeKeyGen_some rfl h

theorem kpkeKeyGen1024_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < 4) (hj : j < 4)
    (h : sampleNTT iters (matSeed (kgRho1024 d) i j) = none) : kpkeKeyGen mlKem1024 iters d = none :=
  KPke.kpkeKeyGen_none hi hj h

theorem kpkeEncrypt1024_some {iters : Nat} {ek m r : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (ekRho mlKem1024 ek) i j) = some (a i j)) :
    kpkeEncrypt mlKem1024 iters ek m r = some (ct1024 a ek m r) :=
  KPke.kpkeEncrypt_some ⟨rfl, rfl⟩ h

theorem kpkeEncrypt1024_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < 4) (hj : j < 4)
    (h : sampleNTT iters (matSeed (ekRho mlKem1024 ek) i j) = none) :
    kpkeEncrypt mlKem1024 iters ek m r = none :=
  KPke.kpkeEncrypt_none hi hj h

theorem kpkeDecrypt1024 (dk c : List Byte) :
    kpkeDecrypt mlKem1024 dk c =
      compressEncode 1 (sub (dcV1024 c) (nttInv (dot4 (dcS dk) fun i => ntt (dcU1024 c i)))) :=
  KPke.kpkeDecrypt_eq mlKem1024 dk c

theorem keyGenInternal1024 (iters : Nat) (d z : List Byte) :
    keyGenInternal mlKem1024 iters d z =
      (kpkeKeyGen mlKem1024 iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) :=
  KPke.keyGenInternal_eq mlKem1024 iters d z

theorem encapsInternal1024 (iters : Nat) (ek m : List Byte) :
    encapsInternal mlKem1024 iters ek m =
      (kpkeEncrypt mlKem1024 iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) :=
  KPke.encapsInternal_eq mlKem1024 iters ek m

theorem decapsInternal1024 (iters : Nat) (dk c : List Byte) :
    decapsInternal mlKem1024 iters dk c =
      (kpkeEncrypt mlKem1024 iters (dkEk1024 dk) (decM1024 dk c)
          (G (decM1024 dk c ++ dkH1024 dk)).2).map fun c' =>
        if c = c' then (G (decM1024 dk c ++ dkH1024 dk)).1 else J (dkZ1024 dk ++ c) :=
  KPke.decapsInternal_eq mlKem1024 iters dk c

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Ntt`. -/
section

/-!
# ML-KEM: the NTT as butterflies, for every target

`NTT` (Algorithm 9) and `NTT⁻¹` (Algorithm 10) restated as the loops an
implementation runs, so that its proof is only about its instructions:

* the tables `zetas` (`ζ^BitRev7(k) mod q`, FIPS 203 Appendix A) and
  `gammas` (`ζ^(2BitRev7(i)+1) mod q`, for `MultiplyNTTs`), as numbers;
* one butterfly, `bfly` (Algorithm 9, lines 8–10) or `bflyInv` (Algorithm
  10, lines 8–10), and what it does to each coefficient (`bfly_get`,
  `bflyInv_get`);
* the three nested loops: `ntt f` is `nttLayer` for each `len` of `nttLens`,
  a layer is `nttBlock` for each of its blocks, and a block is `len`
  butterflies. `nttBlockN` and `nttLayerN` are the loops after their first
  `t` iterations (`…_zero`, `…_succ`), for loop invariants, and
  `nttBlockN_get` says what each coefficient is after `t` butterflies of a
  block. Likewise `nttInvLayer`, `nttInvBlock`, `nttInvBlockN`;
* the flat list of butterflies (`ntt_eq_ops`, `nttInv_eq_ops`);
* `MultiplyNTTs` coefficient by coefficient (`multiplyNTTs_even`,
  `multiplyNTTs_odd`).

The zeta of the block `b` of the layer with `len` (`k` in the loops, `i` in
the standard) is `128 / len + b` in `NTT` (the standard's counter `i` runs
from 1 up) and `256 / len - 1 - b` in `NTT⁻¹` (from 127 down).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## The tables -/

/-- `ζ^BitRev7(k) mod q` for `k < 128` (FIPS 203 Appendix A), the zetas of
the NTT. -/
def zetas : List Nat := [
  1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296,
  2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331,
  3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319, 1435,
  807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910, 17, 2761, 583,
  2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789,
  1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641, 1584, 2298, 2037,
  3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594, 2804, 1092, 403,
  1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- `ζ^(2BitRev7(i) + 1) mod q` for `i < 128` (FIPS 203 Appendix A), the
moduli `γ` of `MultiplyNTTs`. -/
def gammas : List Nat := [
  17, 3312, 2761, 568, 583, 2746, 2649, 680, 1637, 1692, 723, 2606, 2288, 1041, 1100, 2229, 1409,
  1920, 2662, 667, 3281, 48, 233, 3096, 756, 2573, 2156, 1173, 3015, 314, 3050, 279, 1703, 1626,
  1651, 1678, 2789, 540, 1789, 1540, 1847, 1482, 952, 2377, 1461, 1868, 2687, 642, 939, 2390,
  2308, 1021, 2437, 892, 2388, 941, 733, 2596, 2337, 992, 268, 3061, 641, 2688, 1584, 1745, 2298,
  1031, 2037, 1292, 3220, 109, 375, 2954, 2549, 780, 2090, 1239, 1645, 1684, 1063, 2266, 319,
  3010, 2773, 556, 757, 2572, 2099, 1230, 561, 2768, 2466, 863, 2594, 735, 2804, 525, 1092, 2237,
  403, 2926, 1026, 2303, 1143, 2186, 2150, 1179, 2775, 554, 886, 2443, 1722, 1607, 1212, 2117,
  1874, 1455, 1029, 2300, 2110, 1219, 2935, 394, 885, 2444, 2154, 1175]

/-- `ζ^BitRev7(k)`. -/
def zeta (k : Nat) : Zq := ζ ^ bitRev7 k

/-- `γ = ζ^(2BitRev7(i) + 1)`, the modulus of the `i`-th product of
`MultiplyNTTs`. -/
def gamma (i : Nat) : Zq := ζ ^ (2 * bitRev7 i + 1)

theorem zetas_length : zetas.length = 128 := by decide +kernel

theorem gammas_length : gammas.length = 128 := by decide +kernel

/-- Entry `j` of `l` is `f (i + j)`, for each entry: a `List.rec` over `Nat.beq`,
which the kernel evaluates in one pass (rather than `getD` for each index). -/
private noncomputable def listIs (f : Nat → Nat) (l : List Nat) : Nat → Bool :=
  List.rec (fun _ => true) (fun a _ ih i => Nat.beq a (f i) && ih (i + 1)) l

private theorem listIs_spec {f : Nat → Nat} {l : List Nat} {i : Nat} (h : listIs f l i = true) :
    ∀ j < l.length, l.getD j 0 = f (i + j) := by
  induction l generalizing i with
  | nil => intro j hj; simp at hj
  | cons a l ih =>
    simp only [listIs, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero => simpa using Nat.eq_of_beq_eq_true h.1
    | succ j =>
      have := ih h.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      simpa using this

private theorem zetas_nat : ∀ i < 128, zetas.getD i 0 = 17 ^ bitRev7 i % 3329 := by
  intro i hi
  have := listIs_spec (f := fun i => 17 ^ bitRev7 i % 3329) (l := zetas) (i := 0) (by decide +kernel) i
    (by rw [zetas_length]; exact hi)
  simpa using this

private theorem gammas_nat : ∀ i < 128, gammas.getD i 0 = 17 ^ (2 * bitRev7 i + 1) % 3329 := by
  intro i hi
  have := listIs_spec (f := fun i => 17 ^ (2 * bitRev7 i + 1) % 3329) (l := gammas) (i := 0)
    (by decide +kernel) i (by rw [gammas_length]; exact hi)
  simpa using this

/-- Entry `k` of `zetas` is `ζ^BitRev7(k)`. -/
theorem zetas_getD {k : Nat} (hk : k < 128) : zetas.getD k 0 = (zeta k).val := by
  rw [zetas_nat k hk, zeta, val_pow]; rfl

/-- Entry `i` of `gammas` is `ζ^(2BitRev7(i) + 1)`. -/
theorem gammas_getD {i : Nat} (hi : i < 128) : gammas.getD i 0 = (gamma i).val := by
  rw [gammas_nat i hi, gamma, val_pow]; rfl

theorem zetas_getElem {k : Nat} (hk : k < 128) :
    zetas[k]'(by rw [zetas_length]; exact hk) = (zeta k).val := by
  rw [← zetas_getD hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem gammas_getElem {i : Nat} (hi : i < 128) :
    gammas[i]'(by rw [gammas_length]; exact hi) = (gamma i).val := by
  rw [← gammas_getD hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem zeta_eq {k : Nat} (hk : k < 128) : zeta k = ofNat (zetas.getD k 0) := by
  rw [zetas_getD hk, ofNat_val]

theorem gamma_eq {i : Nat} (hi : i < 128) : gamma i = ofNat (gammas.getD i 0) := by
  rw [gammas_getD hi, ofNat_val]

/-! ## Butterflies -/

/-- The butterfly of Algorithm 9 (lines 8–10) on `f[j]` and `f[j + len]`
with the zeta `z`: `t ← z · f[j + len]`, `f[j + len] ← f[j] - t`,
`f[j] ← f[j] + t`. -/
def bfly (f : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := z * f[j + len]!
  let g := f.set! (j + len) (f[j]! - t)
  g.set! j (g[j]! + t)

/-- The butterfly of Algorithm 10 (lines 8–10) on `f[j]` and `f[j + len]`
with the zeta `z`: `t ← f[j]`, `f[j] ← t + f[j + len]`,
`f[j + len] ← z · (f[j + len] - t)`. -/
def bflyInv (f : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := f[j]!
  let g := f.set! j (t + f[j + len]!)
  g.set! (j + len) (z * (g[j + len]! - t))

/-- A butterfly changes `f[j]` to `f[j] + z·f[j + len]` and `f[j + len]` to
`f[j] - z·f[j + len]`, and nothing else. -/
theorem bfly_get (f : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bfly f j len z)[i]! =
      if i = j then f[j]! + z * f[j + len]!
      else if i = j + len then f[j]! - z * f[j + len]!
      else f[i]! := by
  simp only [bfly]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_self _ hi, getElem!_set!_ne _ hi (by omega), ite_eq_left rfl]
  · rw [getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), ite_eq_right h2]

/-- An inverse butterfly changes `f[j]` to `f[j] + f[j + len]` and
`f[j + len]` to `z·(f[j + len] - f[j])`, and nothing else. -/
theorem bflyInv_get (f : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bflyInv f j len z)[i]! =
      if i = j then f[j]! + f[j + len]!
      else if i = j + len then z * (f[j + len]! - f[j]!)
      else f[i]! := by
  simp only [bflyInv]
  rw [getElem!_set!_ne _ hj (by omega)]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_ne _ hi (by omega), getElem!_set!_self _ hi, ite_eq_left rfl]
  · rw [ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h2]

/-! ## Loops -/

theorem foldl_range'_succ {α : Type} (g : α → Nat → α) (x : α) (s t : Nat) :
    (List.range' s (t + 1)).foldl g x = g ((List.range' s t).foldl g x) (s + t) := by
  rw [List.range'_concat, List.foldl_append, Nat.one_mul]; rfl

theorem foldl_range_succ {α : Type} (g : α → Nat → α) (x : α) (t : Nat) :
    (List.range (t + 1)).foldl g x = g ((List.range t).foldl g x) t := by
  rw [List.range_succ, List.foldl_append]; rfl

/-! ## NTT -/

/-- The first `t` iterations of the innermost loop of Algorithm 9 for the
block from `start` of the layer with `len`, whose zeta is `zeta k`. -/
def nttBlockN (f : Poly) (len k start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => bfly f j len (zeta k)) f

/-- The innermost loop of Algorithm 9: the `len` butterflies of a block. -/
def nttBlock (f : Poly) (len k start : Nat) : Poly := nttBlockN f len k start len

/-- The first `b` iterations of the middle loop of Algorithm 9 for the layer
with `len`: blocks `0 … b - 1`, block `c` from `2 · len · c` with the zeta
`zeta (128 / len + c)`. -/
def nttLayerN (f : Poly) (len b : Nat) : Poly :=
  (List.range b).foldl (fun f c => nttBlock f len (128 / len + c) (2 * len * c)) f

/-- The middle loop of Algorithm 9: the `128 / len` blocks of the layer with
`len`. -/
def nttLayer (f : Poly) (len : Nat) : Poly := nttLayerN f len (128 / len)

/-- The values of `len` of the layers of Algorithm 9, in order. -/
def nttLens : List Nat := [128, 64, 32, 16, 8, 4, 2]

theorem nttBlockN_zero (f : Poly) (len k start : Nat) : nttBlockN f len k start 0 = f := rfl

theorem nttBlockN_succ (f : Poly) (len k start t : Nat) :
    nttBlockN f len k start (t + 1) = bfly (nttBlockN f len k start t) (start + t) len (zeta k) :=
  foldl_range'_succ _ _ _ _

theorem nttLayerN_zero (f : Poly) (len : Nat) : nttLayerN f len 0 = f := rfl

theorem nttLayerN_succ (f : Poly) (len b : Nat) :
    nttLayerN f len (b + 1) = nttBlock (nttLayerN f len b) len (128 / len + b) (2 * len * b) :=
  foldl_range_succ _ _ _

/-- Each coefficient after the first `t` butterflies of a block: the
butterflies on `(j, j + len)` for `start ≤ j < start + t` are done. -/
theorem nttBlockN_get (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (nttBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + zeta k * f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then f[i - len]! - zeta k * f[i]!
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttBlockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- A whole block. -/
theorem nttBlock_get (f : Poly) {len k start : Nat} (hlen : 0 < len) (hs : start + 2 * len ≤ n)
    {i : Nat} (hi : i < n) :
    (nttBlock f len k start)[i]! =
      if start ≤ i ∧ i < start + len then f[i]! + zeta k * f[i + len]!
      else if start + len ≤ i ∧ i < start + 2 * len then f[i - len]! - zeta k * f[i]!
      else f[i]! := by
  rw [nttBlock, nttBlockN_get f hlen (Nat.le_refl _) hs hi, show start + len + len = start + 2 * len by
    omega]

/-- A step of the middle loop of Algorithm 9 with the counter `i`, as the
standard writes it. -/
private def nttMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (nttBlock b.1 len b.2 start, b.2 + 1)

/-- A step of the outer loop of Algorithm 9 with the counter `i`. -/
private def nttOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttMid len) b

private theorem ntt_eq_outer (f : Poly) : ntt f = (nttLens.foldl nttOuter (f, 1)).1 := by
  simp only [ntt, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  rfl

private theorem foldl_nttMid (len st i : Nat) (f : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttMid len) (f, i) =
      ((List.range cnt).foldl (fun g c => nttBlock g len (i + c) (st * c)) f, i + cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttMid len st i f cnt, foldl_range_succ,
      Nat.zero_add]
    rfl

private theorem nttOuter_eq (f : Poly) (len i : Nat) :
    nttOuter (f, i) len = ((List.range (n / (2 * len))).foldl
      (fun g c => nttBlock g len (i + c) (2 * len * c)) f, i + n / (2 * len)) :=
  foldl_nttMid _ _ _ _ _

/-- `NTT` is its seven layers, in order. -/
theorem ntt_eq_layers (f : Poly) : ntt f = nttLens.foldl nttLayer f := by
  rw [ntt_eq_outer]
  simp only [nttLens, List.foldl_cons, List.foldl_nil, nttOuter_eq, nttLayer, nttLayerN, n,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd]

/-- The butterflies of Algorithm 9, in order: `(j, len, k)` for the
butterfly on `f[j]` and `f[j + len]` with the zeta `zeta k`. -/
def nttOps : List (Nat × Nat × Nat) :=
  nttLens.flatMap fun len => (List.range (128 / len)).flatMap fun c =>
    (List.range' (2 * len * c) len).map fun j => (j, len, 128 / len + c)

/-- `NTT` is its 896 butterflies, in order. -/
theorem ntt_eq_ops (f : Poly) : ntt f = nttOps.foldl (fun f o => bfly f o.1 o.2.1 (zeta o.2.2)) f := by
  simp only [ntt_eq_layers, nttOps, List.foldl_flatMap, List.foldl_map]
  rfl

/-! ## NTT⁻¹ -/

/-- The first `t` iterations of the innermost loop of Algorithm 10 for the
block from `start` of the layer with `len`, whose zeta is `zeta k`. -/
def nttInvBlockN (f : Poly) (len k start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => bflyInv f j len (zeta k)) f

/-- The innermost loop of Algorithm 10: the `len` butterflies of a block. -/
def nttInvBlock (f : Poly) (len k start : Nat) : Poly := nttInvBlockN f len k start len

/-- The first `b` iterations of the middle loop of Algorithm 10 for the
layer with `len`: blocks `0 … b - 1`, block `c` from `2 · len · c` with the
zeta `zeta (256 / len - 1 - c)`. -/
def nttInvLayerN (f : Poly) (len b : Nat) : Poly :=
  (List.range b).foldl (fun f c => nttInvBlock f len (256 / len - 1 - c) (2 * len * c)) f

/-- The middle loop of Algorithm 10: the `128 / len` blocks of the layer
with `len`. -/
def nttInvLayer (f : Poly) (len : Nat) : Poly := nttInvLayerN f len (128 / len)

/-- The values of `len` of the layers of Algorithm 10, in order. -/
def nttInvLens : List Nat := [2, 4, 8, 16, 32, 64, 128]

theorem nttInvBlockN_zero (f : Poly) (len k start : Nat) : nttInvBlockN f len k start 0 = f := rfl

theorem nttInvBlockN_succ (f : Poly) (len k start t : Nat) :
    nttInvBlockN f len k start (t + 1) =
      bflyInv (nttInvBlockN f len k start t) (start + t) len (zeta k) :=
  foldl_range'_succ _ _ _ _

theorem nttInvLayerN_zero (f : Poly) (len : Nat) : nttInvLayerN f len 0 = f := rfl

theorem nttInvLayerN_succ (f : Poly) (len b : Nat) :
    nttInvLayerN f len (b + 1) =
      nttInvBlock (nttInvLayerN f len b) len (256 / len - 1 - b) (2 * len * b) :=
  foldl_range_succ _ _ _

/-- Each coefficient after the first `t` inverse butterflies of a block. -/
theorem nttInvBlockN_get (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (nttInvBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then zeta k * (f[i]! - f[i - len]!)
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttInvBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttInvBlockN_succ, bflyInv_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- A whole inverse block. -/
theorem nttInvBlock_get (f : Poly) {len k start : Nat} (hlen : 0 < len) (hs : start + 2 * len ≤ n)
    {i : Nat} (hi : i < n) :
    (nttInvBlock f len k start)[i]! =
      if start ≤ i ∧ i < start + len then f[i]! + f[i + len]!
      else if start + len ≤ i ∧ i < start + 2 * len then zeta k * (f[i]! - f[i - len]!)
      else f[i]! := by
  rw [nttInvBlock, nttInvBlockN_get f hlen (Nat.le_refl _) hs hi,
    show start + len + len = start + 2 * len by omega]

/-- A step of the middle loop of Algorithm 10 with the counter `i`, as the
standard writes it. -/
private def nttInvMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (nttInvBlock b.1 len b.2 start, b.2 - 1)

/-- A step of the outer loop of Algorithm 10 with the counter `i`. -/
private def nttInvOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttInvMid len) b

private theorem nttInv_eq_outer (f : Poly) :
    nttInv f = ((nttInvLens.foldl nttInvOuter (f, 127)).1).map (· * 3303) := by
  simp only [nttInv, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  rfl

private theorem foldl_nttInvMid (len st i : Nat) (f : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttInvMid len) (f, i) =
      ((List.range cnt).foldl (fun g c => nttInvBlock g len (i - c) (st * c)) f, i - cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttInvMid len st i f cnt, foldl_range_succ,
      Nat.zero_add]
    rfl

private theorem nttInvOuter_eq (f : Poly) (len i : Nat) :
    nttInvOuter (f, i) len = ((List.range (n / (2 * len))).foldl
      (fun g c => nttInvBlock g len (i - c) (2 * len * c)) f, i - n / (2 * len)) :=
  foldl_nttInvMid _ _ _ _ _

/-- `NTT⁻¹` is its seven layers, in order, and the multiplication of every
coefficient by `3303 = 128⁻¹ mod q`. -/
theorem nttInv_eq_layers (f : Poly) :
    nttInv f = (nttInvLens.foldl nttInvLayer f).map (· * 3303) := by
  rw [nttInv_eq_outer]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil, nttInvOuter_eq, nttInvLayer,
    nttInvLayerN, n, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]

/-- The butterflies of Algorithm 10, in order: `(j, len, k)` for the
inverse butterfly on `f[j]` and `f[j + len]` with the zeta `zeta k`. -/
def nttInvOps : List (Nat × Nat × Nat) :=
  nttInvLens.flatMap fun len => (List.range (128 / len)).flatMap fun c =>
    (List.range' (2 * len * c) len).map fun j => (j, len, 256 / len - 1 - c)

/-- `NTT⁻¹` is its 896 butterflies, in order, and the multiplication by
3303. -/
theorem nttInv_eq_ops (f : Poly) :
    nttInv f = (nttInvOps.foldl (fun f o => bflyInv f o.1 o.2.1 (zeta o.2.2)) f).map (· * 3303) := by
  simp only [nttInv_eq_layers, nttInvOps, List.foldl_flatMap, List.foldl_map]
  rfl

/-- The last step of `NTT⁻¹`, coefficient by coefficient. -/
theorem map_mul_get (f : Poly) {i : Nat} (hi : i < n) : (f.map (· * 3303))[i]! = f[i]! * 3303 := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_map]

/-! ## Blocks, some butterflies at a time -/

theorem nttBlockN_add (f : Poly) (len k start t t' : Nat) :
    nttBlockN f len k start (t + t') = nttBlockN (nttBlockN f len k start t) len k (start + t) t' := by
  simp only [nttBlockN]; rw [← List.foldl_append, List.range'_append_1]

theorem nttInvBlockN_add (f : Poly) (len k start t t' : Nat) :
    nttInvBlockN f len k start (t + t') =
      nttInvBlockN (nttInvBlockN f len k start t) len k (start + t) t' := by
  simp only [nttInvBlockN]; rw [← List.foldl_append, List.range'_append_1]

/-- `nttBlockN_get`, for the butterflies of the block up to `start + t`
only. -/
theorem nttBlockN_get' (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (nttBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + zeta k * f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then f[i - len]! - zeta k * f[i]!
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttBlockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

theorem nttInvBlockN_get' (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (nttInvBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then zeta k * (f[i]! - f[i - len]!)
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttInvBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttInvBlockN_succ, bflyInv_get _ hlen (by omega) _ hi,
      ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-! ## MultiplyNTTs -/

/-- Coefficient `2i` of `MultiplyNTTs(f, g)`: `f[2i]·g[2i] + f[2i+1]·g[2i+1]·γᵢ`. -/
theorem multiplyNTTs_even (f g : Poly) {i : Nat} (hi : i < 128) :
    (multiplyNTTs f g)[2 * i]! =
      f[2 * i]! * g[2 * i]! + f[2 * i + 1]! * g[2 * i + 1]! * gamma i := by
  rw [getElem!_eq _ (by rw [n_eq]; omega), multiplyNTTs, Vector.getElem_ofFn]
  dsimp only
  rw [show 2 * i / 2 = i by omega, ite_eq_left (show 2 * i % 2 = 0 by omega)]
  rfl

/-- Coefficient `2i + 1` of `MultiplyNTTs(f, g)`: `f[2i]·g[2i+1] + f[2i+1]·g[2i]`. -/
theorem multiplyNTTs_odd (f g : Poly) {i : Nat} (hi : i < 128) :
    (multiplyNTTs f g)[2 * i + 1]! = f[2 * i]! * g[2 * i + 1]! + f[2 * i + 1]! * g[2 * i]! := by
  rw [getElem!_eq _ (by rw [n_eq]; omega), multiplyNTTs, Vector.getElem_ofFn]
  dsimp only
  rw [show (2 * i + 1) / 2 = i by omega, ite_eq_right (show ¬ (2 * i + 1) % 2 = 0 by omega)]
  rfl

/-- Any coefficient of `MultiplyNTTs(f, g)`. -/
theorem multiplyNTTs_get (f g : Poly) {h : Nat} (hh : h < n) :
    (multiplyNTTs f g)[h]! =
      if h % 2 = 0 then
        f[h]! * g[h]! + f[h + 1]! * g[h + 1]! * gamma (h / 2)
      else f[h - 1]! * g[h]! + f[h]! * g[h - 1]! := by
  rw [n_eq] at hh
  split
  · have := multiplyNTTs_even f g (i := h / 2) (by omega)
    rwa [show 2 * (h / 2) = h by omega] at this
  · have := multiplyNTTs_odd f g (i := h / 2) (by omega)
    rwa [show 2 * (h / 2) + 1 = h by omega, show 2 * (h / 2) = h - 1 by omega] at this

end VG.Proof.MlKem

end
