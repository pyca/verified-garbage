import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.Mul32`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.Zq`. -/
section

/-!
# ML-DSA: arithmetic modulo `q`, for every target

Facts about `ℤ_q` (`Fin q`, `q = 8380417`) as the natural numbers that
represent its elements, and the recipes that implementations reduce modulo `q`
with, each proven for every input in its range:

* addition and subtraction of reduced values, with one conditional
  subtraction of `q` (`val_add`, `val_sub`, `condSub`);
* `barrett`, a Barrett reduction of any `x < 2⁶⁴` with the high half of one
  64×64→128-bit product (`⌊x · ⌊2⁶⁴/q⌋ / 2⁶⁴⌋` is the quotient estimate),
  which leaves a value less than `2q` congruent to `x`, which `condSub` then
  reduces (`reduce_barrett`). A product of two reduced values is less than
  `q² < 2⁴⁶`, so it reduces any such product, or such a product plus a
  reduced value.

It also has the coefficients of polynomials (`getElem!_eq`, `ext_getElem!`)
and of their sums, differences and products (`add_get`, `sub_get`,
`mul_get`).
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-! ## `ℤ_q` as natural numbers -/

theorem q_eq : q = 8380417 := rfl

theorem n_eq : n = 256 := rfl

/-- The element of `ℤ_q` that `x` represents, `x mod q`. -/
abbrev ofNat (x : Nat) : Zq := Fin.ofNat q x

theorem val_ofNat (x : Nat) : (VG.Proof.MlDsa.Arith.ofNat x).val = x % q := rfl

theorem ofNat_val (a : Zq) : VG.Proof.MlDsa.Arith.ofNat a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem ofNat_of_lt {x : Nat} (h : x < q) : (VG.Proof.MlDsa.Arith.ofNat x).val = x := Nat.mod_eq_of_lt h

theorem val_add' (a b : Zq) : (a + b).val = (a.val + b.val) % q := Fin.val_add a b

theorem val_sub' (a b : Zq) : (a - b).val = (a.val + (q - b.val)) % q := by
  rw [Fin.val_sub, Nat.add_comm]

theorem val_mul (a b : Zq) : (a * b).val = a.val * b.val % q := Fin.val_mul a b

theorem val_neg (a : Zq) : (-a).val = (q - a.val) % q := Fin.val_neg' a

theorem val_pow (a : Zq) (k : Nat) : (a ^ k).val = a.val ^ k % q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (a ^ k * a).val = _
    rw [VG.Proof.MlDsa.Arith.val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

/-- The integer that represents an element of `ℤ_q` is less than 8380417. -/
theorem val_lt (a : Zq) : a.val < 8380417 := a.isLt

/-! ## Coefficients of polynomials -/

theorem getElem!_eq (f : Poly) {i : Nat} (hi : i < n) : f[i]! = f[i] := getElem!_pos f i hi

theorem getElem!_set!_self (f : Poly) {i : Nat} (hi : i < n) (x : Zq) : (f.set! i x)[i]! = x := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi, Vector.getElem_set!, ite_eq_left rfl]

theorem getElem!_set!_ne (f : Poly) {i j : Nat} (hj : j < n) (h : i ≠ j) (x : Zq) :
    (f.set! i x)[j]! = f[j]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hj, VG.Proof.MlDsa.Arith.getElem!_eq _ hj, Vector.getElem_set!, ite_eq_right h]

theorem ext_getElem! {f g : Poly} (h : ∀ i < n, f[i]! = g[i]!) : f = g :=
  Vector.ext fun i hi => by rw [← VG.Proof.MlDsa.Arith.getElem!_eq f hi, ← VG.Proof.MlDsa.Arith.getElem!_eq g hi]; exact h i hi

theorem add_get (f g : Poly) {i : Nat} (hi : i < n) : (add f g)[i]! = f[i]! + g[i]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [add, Vector.getElem_zipWith]

theorem sub_get (f g : Poly) {i : Nat} (hi : i < n) : (VG.Spec.MlDsa.sub f g)[i]! = f[i]! - g[i]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [VG.Spec.MlDsa.sub, Vector.getElem_zipWith]

theorem mul_get (f g : Poly) {i : Nat} (hi : i < n) : (multiplyNTT f g)[i]! = f[i]! * g[i]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [multiplyNTT, Vector.getElem_zipWith]

/-- A coefficient of `f` with each coefficient multiplied by `c`. -/
theorem map_mul_get (f : Poly) (c : Zq) {i : Nat} (hi : i < n) : (f.map (· * c))[i]! = f[i]! * c := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi, VG.Proof.MlDsa.Arith.getElem!_eq _ hi, Vector.getElem_map]

/-! ## Addition and subtraction of reduced values -/

/-- One conditional subtraction of `q`. -/
def condSub (t : Nat) : Nat := if q ≤ t then t - q else t

/-- One conditional subtraction reduces a value less than `2q`. -/
theorem condSub_eq {t : Nat} (h : t < 2 * q) : VG.Proof.MlDsa.Arith.condSub t = t % q := by
  unfold VG.Proof.MlDsa.Arith.condSub; rw [VG.Proof.MlDsa.Arith.q_eq] at *; split <;> omega

theorem condSub_lt {t : Nat} (h : t < 2 * q) : VG.Proof.MlDsa.Arith.condSub t < q := by
  unfold VG.Proof.MlDsa.Arith.condSub; rw [VG.Proof.MlDsa.Arith.q_eq] at *; split <;> omega

theorem val_add (a b : Zq) : (a + b).val = VG.Proof.MlDsa.Arith.condSub (a.val + b.val) := by
  rw [VG.Proof.MlDsa.Arith.val_add', VG.Proof.MlDsa.Arith.condSub_eq (by have := a.isLt; have := b.isLt; omega)]

theorem val_sub (a b : Zq) : (a - b).val = VG.Proof.MlDsa.Arith.condSub (a.val + q - b.val) := by
  have := a.isLt; have := b.isLt
  rw [VG.Proof.MlDsa.Arith.val_sub', VG.Proof.MlDsa.Arith.condSub_eq (by omega), show a.val + (q - b.val) = a.val + q - b.val by omega]

/-! ## Barrett reduction with the high half of a 128-bit product -/

/-- `⌊2⁶⁴ / q⌋`. -/
def barrettM : Nat := 2201172575745

theorem barrettM_eq : VG.Proof.MlDsa.Arith.barrettM = 2 ^ 64 / q := by decide

/-- The quotient estimate of `barrett`: the high half of `x · ⌊2⁶⁴ / q⌋`. -/
def barrettQuot (x : Nat) : Nat := x * VG.Proof.MlDsa.Arith.barrettM / 2 ^ 64

/-- `x - ⌊…⌋ · q`: `x` reduced to less than `2q` (`barrett_lt`). -/
def barrett (x : Nat) : Nat := x - VG.Proof.MlDsa.Arith.barrettQuot x * q

/-- For `x < 2⁶⁴`: the estimate times `q` is at most `x`, and `x` is less
than the estimate plus 2, times `q`. -/
theorem barrett_bounds {x : Nat} (hx : x < 2 ^ 64) :
    VG.Proof.MlDsa.Arith.barrettQuot x * q ≤ x ∧ x < VG.Proof.MlDsa.Arith.barrettQuot x * q + 2 * q := by
  unfold VG.Proof.MlDsa.Arith.barrettQuot VG.Proof.MlDsa.Arith.barrettM
  rw [VG.Proof.MlDsa.Arith.q_eq]
  constructor <;> omega

theorem barrett_lt {x : Nat} (hx : x < 2 ^ 64) : VG.Proof.MlDsa.Arith.barrett x < 2 * q := by
  have := VG.Proof.MlDsa.Arith.barrett_bounds hx
  unfold VG.Proof.MlDsa.Arith.barrett
  omega

theorem barrett_mod {x : Nat} (hx : x < 2 ^ 64) : VG.Proof.MlDsa.Arith.barrett x % q = x % q := by
  have h := (VG.Proof.MlDsa.Arith.barrett_bounds hx).1
  unfold VG.Proof.MlDsa.Arith.barrett
  generalize VG.Proof.MlDsa.Arith.barrettQuot x = e at h
  have := Nat.mul_mod_left e q
  rw [VG.Proof.MlDsa.Arith.q_eq] at *
  omega

/-- Reduction modulo `q` of `x < 2⁶⁴`. -/
theorem reduce_barrett {x : Nat} (hx : x < 2 ^ 64) : VG.Proof.MlDsa.Arith.condSub (VG.Proof.MlDsa.Arith.barrett x) = x % q := by
  rw [VG.Proof.MlDsa.Arith.condSub_eq (VG.Proof.MlDsa.Arith.barrett_lt hx), VG.Proof.MlDsa.Arith.barrett_mod hx]

/-- A product of reduced values is less than `q² < 2⁴⁶`. -/
theorem mul_lt_q2 {a b : Nat} (ha : a < q) (hb : b < q) : a * b < 70231389093889 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt ha hb) (by decide)

end VG.Proof.MlDsa.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.Mem`. -/
section

/-!
# ML-DSA: polynomials in memory, for every target

How the stored representation of `Spec/MlDsa/Poly.lean` (a polynomial as
`[u32; 256]`, `coeffAt`, `polyAt`, `Reduced`, `PolyIs`) changes when a program
writes a coefficient, and how to conclude `PolyIs` from what each word holds.
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (VG.Proof.MlDsa.Arith.coeffAddr p i) 32 := rfl

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < n) : (VG.Proof.MlDsa.Arith.polyRegion p).Contains (VG.Proof.MlDsa.Arith.coeffAddr p i) 4 := by
  rw [VG.Proof.MlDsa.Arith.n_eq] at hi; exact Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    Mem.Sep (VG.Proof.MlDsa.Arith.coeffAddr p i) 4 (VG.Proof.MlDsa.Arith.coeffAddr p j) 4 := by
  rw [VG.Proof.MlDsa.Arith.n_eq] at hi hj; exact Offset.sep p (by omega) (by omega) (by omega)

theorem coeffAddr_add (p : Addr) (j len : Nat) :
    VG.Proof.MlDsa.Arith.coeffAddr p j + BitVec.ofNat 64 (4 * len) = VG.Proof.MlDsa.Arith.coeffAddr p (j + len) := by
  rw [VG.Proof.MlDsa.Arith.coeffAddr, VG.Proof.MlDsa.Arith.coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem coeffAddr_succ (p : Addr) (j : Nat) : VG.Proof.MlDsa.Arith.coeffAddr p j + 4 = VG.Proof.MlDsa.Arith.coeffAddr p (j + 1) :=
  VG.Proof.MlDsa.Arith.coeffAddr_add p j 1

theorem coeffAt_writeW_self (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) :
    coeffAt (m.writeW (VG.Proof.MlDsa.Arith.coeffAddr p i) v) p i = v :=
  Mem.readW_writeW_self32 m _ v

theorem coeffAt_writeW_ne (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j)
    (v : BitVec 32) : coeffAt (m.writeW (VG.Proof.MlDsa.Arith.coeffAddr p j) v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep (VG.Proof.MlDsa.Arith.coeff_sep p hi hj h) (by decide)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (v : BitVec 32) :
    coeffAt (m.writeW (VG.Proof.MlDsa.Arith.coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact VG.Proof.MlDsa.Arith.coeffAt_writeW_self m p i v
  · exact VG.Proof.MlDsa.Arith.coeffAt_writeW_ne m p hi hj (Ne.symm ‹_›) v

/-- Coefficient `i` of `polyAt`: the stored word modulo `q`. -/
theorem polyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i]! = VG.Proof.MlDsa.Arith.ofNat (coeffAt m p i).toNat := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [polyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]!).val = (coeffAt m p i).toNat := by
  rw [VG.Proof.MlDsa.Arith.polyAt_get m p hi, VG.Proof.MlDsa.Arith.ofNat_of_lt (hr i hi)]

theorem reduced_writeW {m : Mem} {p : Addr} (hr : Reduced m p) {j : Nat} (hj : j < n) {v : BitVec 32}
    (hv : v.toNat < q) : Reduced (m.writeW (VG.Proof.MlDsa.Arith.coeffAddr p j) v) p := fun i hi => by
  rw [VG.Proof.MlDsa.Arith.coeffAt_writeW m p hi hj]
  split
  · exact hv
  · exact hr i hi

/-- The word stored for coefficient `i` of `f`. -/
theorem polyIs_toNat {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    (coeffAt m p i).toNat = (f[i]!).val := by
  rw [← h.2, VG.Proof.MlDsa.Arith.polyAt_val h.1 hi]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAt m p i).toNat = (f[i]!).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => ?_⟩
  rw [VG.Proof.MlDsa.Arith.polyAt_get _ _ hi, h i hi, VG.Proof.MlDsa.Arith.ofNat_val]

/-- Writing a coefficient of a stored polynomial: a word whose value is `x`. -/
theorem polyIs_writeW {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {j : Nat} (hj : j < n) (x : Zq)
    {v : BitVec 32} (hv : v.toNat = x.val) : PolyIs (m.writeW (VG.Proof.MlDsa.Arith.coeffAddr p j) v) p (f.set! j x) := by
  refine VG.Proof.MlDsa.Arith.polyIs_of_toNat fun i hi => ?_
  rw [VG.Proof.MlDsa.Arith.coeffAt_writeW m p hi hj]
  split
  · subst j; rw [VG.Proof.MlDsa.Arith.getElem!_set!_self _ hi, hv]
  · rw [VG.Proof.MlDsa.Arith.getElem!_set!_ne _ hi ‹_›, VG.Proof.MlDsa.Arith.polyIs_toNat h hi]

/-! ## Frames: the polynomial is unchanged by writes elsewhere -/

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  rw [VG.Proof.MlDsa.Arith.n_eq] at hi
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) :
    ∀ k < len, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) :=
  fun _ hk => hf.bytes (R := ⟨p, len⟩) hd hlen hk

theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.Arith.polyRegion p).Disjoint r) {i : Nat} (hi : i < n) : coeffAt m' p i = coeffAt m p i :=
  VG.Proof.MlDsa.Arith.coeffAt_congr (VG.Proof.MlDsa.Arith.bytes_frame hf hd (by decide)) hi

theorem polyAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.Arith.polyRegion p).Disjoint r) : polyAt m' p = polyAt m p :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by rw [VG.Proof.MlDsa.Arith.polyAt_get _ _ hi, VG.Proof.MlDsa.Arith.polyAt_get _ _ hi, VG.Proof.MlDsa.Arith.coeffAt_frame hf hd hi]

theorem reduced_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.Arith.polyRegion p).Disjoint r) (hr : Reduced m p) : Reduced m' p := fun i hi => by
  rw [VG.Proof.MlDsa.Arith.coeffAt_frame hf hd hi]; exact hr i hi

theorem polyIs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.Arith.polyRegion p).Disjoint r) (h : PolyIs m p f) : PolyIs m' p f :=
  ⟨VG.Proof.MlDsa.Arith.reduced_frame hf hd h.1, (VG.Proof.MlDsa.Arith.polyAt_frame hf hd).trans h.2⟩

end VG.Proof.MlDsa.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.Mont`. -/
section

/-!
# ML-DSA: Montgomery reduction with 32-bit words, for every target

The reduction a target with 32-bit multiplications (a 32×32→64-bit product)
uses, for `R = 2³²`:

* `mont x = (x + m · q) / 2³²` for `m = (x mod 2³²) · (-q⁻¹ mod 2³²) mod 2³²`
  (`montQInv`): `x + m · q` is a multiple of `2³²` (`mont_mul`), so
  `mont x · 2³² ≡ x (mod q)`, and `mont x < 2q` if `x < q · 2³²`
  (`mont_lt`);
* as 32-bit halves (`mont_halves`): the high half of `x`, plus the high half
  of `m · q`, plus 1 exactly when the low half of `m · q` is not 0 (the
  carry of the sum of the low halves, which is `2³²` or `0`);
* what it computes modulo `q`: for a constant in Montgomery form
  `c · 2³² mod q`, `mont (a · (c · 2³² mod q)) ≡ a · c` (`mont_mulR`); and
  `mont (mont x · (2⁶⁴ mod q)) ≡ x` (`mont_mont_R2`), which multiplies two
  values without a constant in Montgomery form.
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- `-q⁻¹ mod 2³²`. -/
def montQInv : Nat := 4236238847

/-- The multiple of `q` that makes `x` divisible by `2³²`. -/
def montM (x : Nat) : Nat := x % 2 ^ 32 * VG.Proof.MlDsa.Arith.montQInv % 2 ^ 32

/-- The Montgomery reduction of `x`: `(x + m · q) / 2³²`. -/
def mont (x : Nat) : Nat := (x + VG.Proof.MlDsa.Arith.montM x * q) / 2 ^ 32

/-- The low half of `m · q` is `-x mod 2³²`. -/
theorem montM_mul_mod (x : Nat) : VG.Proof.MlDsa.Arith.montM x * q % 2 ^ 32 = x % 2 ^ 32 * 4294967295 % 2 ^ 32 := by
  unfold VG.Proof.MlDsa.Arith.montM
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, show VG.Proof.MlDsa.Arith.montQInv * q % 2 ^ 32 = 4294967295 by decide,
    Nat.mod_mod]

theorem montM_lt (x : Nat) : VG.Proof.MlDsa.Arith.montM x < 2 ^ 32 := Nat.mod_lt _ (by decide)

/-- `x + m · q` is a multiple of `2³²`. -/
theorem mont_mul (x : Nat) : VG.Proof.MlDsa.Arith.mont x * 2 ^ 32 = x + VG.Proof.MlDsa.Arith.montM x * q := by
  have h := VG.Proof.MlDsa.Arith.montM_mul_mod x
  have hd : (x + VG.Proof.MlDsa.Arith.montM x * q) % 2 ^ 32 = 0 :=
    (fun P (h : P % 2 ^ 32 = x % 2 ^ 32 * 4294967295 % 2 ^ 32) => show (x + P) % 2 ^ 32 = 0 by omega) _ h
  unfold VG.Proof.MlDsa.Arith.mont
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)

theorem mont_lt {x : Nat} (hx : x < q * 2 ^ 32) : VG.Proof.MlDsa.Arith.mont x < 2 * q := by
  have h := VG.Proof.MlDsa.Arith.mont_mul x
  have hm : VG.Proof.MlDsa.Arith.montM x * q < 2 ^ 32 * q := Nat.mul_lt_mul_of_pos_right (VG.Proof.MlDsa.Arith.montM_lt x) (by decide)
  rw [VG.Proof.MlDsa.Arith.q_eq] at hx hm ⊢
  exact (fun P (h : VG.Proof.MlDsa.Arith.mont x * 2 ^ 32 = x + P) (hm : P < 2 ^ 32 * 8380417) => show VG.Proof.MlDsa.Arith.mont x < 2 * 8380417 by omega)
    _ h hm

/-- `mont x` from the halves of `x` and of `m · q`, as a 32-bit machine computes it. -/
theorem mont_halves (x : Nat) :
    VG.Proof.MlDsa.Arith.mont x = x / 2 ^ 32 + VG.Proof.MlDsa.Arith.montM x * q / 2 ^ 32 + (if 1 ≤ VG.Proof.MlDsa.Arith.montM x * q % 2 ^ 32 then 1 else 0) := by
  have h := VG.Proof.MlDsa.Arith.montM_mul_mod x
  unfold VG.Proof.MlDsa.Arith.mont
  exact (fun P (h : P % 2 ^ 32 = x % 2 ^ 32 * 4294967295 % 2 ^ 32) =>
    show (x + P) / 2 ^ 32 = x / 2 ^ 32 + P / 2 ^ 32 + (if 1 ≤ P % 2 ^ 32 then 1 else 0) by split <;> omega) _ h

/-- `mont x · 2³² ≡ x (mod q)`. -/
theorem mont_mod (x : Nat) : VG.Proof.MlDsa.Arith.mont x * 2 ^ 32 % q = x % q := by
  rw [VG.Proof.MlDsa.Arith.mont_mul, Nat.add_mul_mod_self_right]

/-- Cancelling the factor `2³²` modulo `q`: `2³² · 8265825 ≡ 1`. -/
theorem cancel_R {u v : Nat} (h : u * 2 ^ 32 % q = v * 2 ^ 32 % q) : u % q = v % q := by
  have e : ∀ w : Nat, w % q = w * 2 ^ 32 % q * 8265825 % q := fun w => by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, show 2 ^ 32 * 8265825 % q = 1 by decide, Nat.mul_one,
      Nat.mod_mod]
  rw [e u, e v, h]

/-- With a constant `c` in Montgomery form: `mont (a · (c · 2³² mod q)) ≡ a · c`. -/
theorem mont_mulR (a c : Nat) : VG.Proof.MlDsa.Arith.mont (a * (c * 2 ^ 32 % q)) % q = a * c % q := by
  refine VG.Proof.MlDsa.Arith.cancel_R ?_
  rw [VG.Proof.MlDsa.Arith.mont_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-- Two reductions, the second of a product with `2⁶⁴ mod q`: `x` modulo `q`. -/
theorem mont_mont_R2 (x : Nat) : VG.Proof.MlDsa.Arith.mont (VG.Proof.MlDsa.Arith.mont x * (2 ^ 64 % q)) % q = x % q := by
  refine VG.Proof.MlDsa.Arith.cancel_R ?_
  rw [VG.Proof.MlDsa.Arith.mont_mod, Nat.mul_mod_mod, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, ← Nat.mul_assoc, Nat.mul_mod,
    VG.Proof.MlDsa.Arith.mont_mod, ← Nat.mul_mod]

/-- `mont` of a value less than `q · 2³²`, reduced by one conditional subtraction. -/
theorem condSub_mont {x : Nat} (hx : x < q * 2 ^ 32) : VG.Proof.MlDsa.Arith.condSub (VG.Proof.MlDsa.Arith.mont x) = VG.Proof.MlDsa.Arith.mont x % q :=
  VG.Proof.MlDsa.Arith.condSub_eq (VG.Proof.MlDsa.Arith.mont_lt hx)

end VG.Proof.MlDsa.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.Mul32`. -/
section

/-!
# ML-DSA: products modulo `q` with 32-bit multiplications, for every target

A target whose only multiplication keeps the low 32 bits of the product
(32-bit ARM, see `TCB/Arm/Isa.lean`) cannot form the product of two reduced
values, which has up to 46 bits. It multiplies `b < q` by `z < 2²³` by
Horner's rule on the pieces `z₂ = ⌊z / 2¹⁴⌋ < 2⁹`, `z₁ = ⌊z / 2⁷⌋ mod 2⁷` and
`z₀ = z mod 2⁷` of `z`, reducing after each step with `red23`, `x - ⌊x / 2²³⌋
· q`, which is congruent to `x` and, for `x < 2³²`, at most `2²³ - 1 + 511 ·
8191` (`red23_le`) as `2²³ - q = 8191`:

`mulzN b z = red23 (b z₀ + 2⁷ · red23 (b z₁ + 2⁷ · red23 (b z₂)))`

is congruent to `b · z` (`mulzN_mod`), and every value on the way is less
than `2³²` (`mulzN_bounds`), and the result less than `2q`.
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- `x - ⌊x / 2²³⌋ · q`. -/
def red23 (x : Nat) : Nat := x - x / 2 ^ 23 * q

/-- The largest value of `red23` on 32 bits. -/
def redMax : Nat := 12574208

theorem red23_le {x : Nat} (hx : x < 2 ^ 32) : VG.Proof.MlDsa.Arith.red23 x ≤ VG.Proof.MlDsa.Arith.redMax := by
  unfold VG.Proof.MlDsa.Arith.red23 VG.Proof.MlDsa.Arith.redMax; rw [VG.Proof.MlDsa.Arith.q_eq]; omega

theorem red23_mod (x : Nat) : VG.Proof.MlDsa.Arith.red23 x % q = x % q := by
  unfold VG.Proof.MlDsa.Arith.red23
  rw [Nat.mul_comm]
  exact Nat.sub_mul_mod (by rw [VG.Proof.MlDsa.Arith.q_eq]; omega)

/-- `(a + x · c) mod q` depends only on `x mod q`. -/
theorem add_mul_mod_congr (a c : Nat) {x y : Nat} (h : x % q = y % q) :
    (a + x * c) % q = (a + y * c) % q := by
  rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

/-- The first step of the product: `red23 (b z₂)`. -/
def mulz1 (b z : Nat) : Nat := VG.Proof.MlDsa.Arith.red23 (b * (z / 16384))

/-- The second step: `red23 (b z₁ + 2⁷ · …)`. -/
def mulz2 (b z : Nat) : Nat := VG.Proof.MlDsa.Arith.red23 (b * (z / 128 % 128) + VG.Proof.MlDsa.Arith.mulz1 b z * 128)

/-- `b · z` modulo `q`, less than `2q`, by Horner's rule on the pieces of `z`. -/
def mulzN (b z : Nat) : Nat := VG.Proof.MlDsa.Arith.red23 (b * (z % 128) + VG.Proof.MlDsa.Arith.mulz2 b z * 128)

theorem mulzN_mod (b z : Nat) : VG.Proof.MlDsa.Arith.mulzN b z % q = b * z % q := by
  unfold VG.Proof.MlDsa.Arith.mulzN VG.Proof.MlDsa.Arith.mulz2 VG.Proof.MlDsa.Arith.mulz1
  have e1 : (b * (z / 128 % 128) + VG.Proof.MlDsa.Arith.red23 (b * (z / 16384)) * 128) % q =
      (b * (z / 128 % 128) + b * (z / 16384) * 128) % q := VG.Proof.MlDsa.Arith.add_mul_mod_congr _ _ (VG.Proof.MlDsa.Arith.red23_mod _)
  rw [VG.Proof.MlDsa.Arith.red23_mod, VG.Proof.MlDsa.Arith.add_mul_mod_congr _ _ ((VG.Proof.MlDsa.Arith.red23_mod _).trans e1)]
  have hz : z % 128 + (z / 128 % 128 + z / 16384 * 128) * 128 = z := by omega
  conv => rhs; rw [← hz]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

/-- The values on the way to `mulzN b z` fit in 32 bits, and the result is
less than `2q`. -/
theorem mulzN_bounds {b z : Nat} (hb : b < q) (hz : z < 2 ^ 23) :
    b * (z / 16384) < 2 ^ 32 ∧ b * (z / 128 % 128) + VG.Proof.MlDsa.Arith.mulz1 b z * 128 < 2 ^ 32 ∧
      b * (z % 128) + VG.Proof.MlDsa.Arith.mulz2 b z * 128 < 2 ^ 32 ∧ VG.Proof.MlDsa.Arith.mulzN b z ≤ VG.Proof.MlDsa.Arith.redMax := by
  rw [VG.Proof.MlDsa.Arith.q_eq] at hb
  have h2 : b * (z / 16384) ≤ 8380416 * 511 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h1 : b * (z / 128 % 128) ≤ 8380416 * 127 := Nat.mul_le_mul (by omega) (by omega)
  have h0 : b * (z % 128) ≤ 8380416 * 127 := Nat.mul_le_mul (by omega) (by omega)
  have r1 : VG.Proof.MlDsa.Arith.mulz1 b z ≤ VG.Proof.MlDsa.Arith.redMax := VG.Proof.MlDsa.Arith.red23_le (by omega)
  have r2 : VG.Proof.MlDsa.Arith.mulz2 b z ≤ VG.Proof.MlDsa.Arith.redMax := VG.Proof.MlDsa.Arith.red23_le (by unfold VG.Proof.MlDsa.Arith.redMax at r1; omega)
  unfold VG.Proof.MlDsa.Arith.redMax at r1 r2
  exact ⟨by omega, by omega, by omega, VG.Proof.MlDsa.Arith.red23_le (by omega)⟩

theorem redMax_lt : VG.Proof.MlDsa.Arith.redMax < 2 * q := by decide

end VG.Proof.MlDsa.Arith

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.Ntt`. -/
section

/-!
# ML-DSA: the NTT as butterflies, for every target

`NTT` (Algorithm 41) and `NTT⁻¹` (Algorithm 42) restated as the loops an
implementation runs, so that its proof is only about its instructions:

* the zetas `zetas m = ζ^BitRev8(m) mod q` as numbers (`zetaNat`);
* one butterfly, `bfly` (Algorithm 41, lines 8–10) or `bflyInv` (Algorithm
  42, lines 8–11), and what it does to each coefficient (`bfly_get`,
  `bflyInv_get`);
* the three nested loops: `ntt f` is `nttLayer` for each `len` of `nttLens`,
  a layer is `blockN` for each of its blocks (`layerN`), and a block is
  `len` butterflies. `blockN` and `layerN` are the loops after their first
  `t` iterations (`…_zero`, `…_succ`), for loop invariants, and
  `blockN_bfly_get` and `blockN_bflyInv_get` say what each coefficient is
  after `t` butterflies of a block. `nttInv f` is likewise `nttInvLayer` for
  each `len` of `nttInvLens`, then the multiplication of every coefficient
  by `256⁻¹ = 8347681`.

The zeta of block `c` of the layer with `len` is `zetas (128 / len + c)` in
`NTT` (the standard's counter `m` runs from 1 up) and
`-zetas (256 / len - 1 - c)` in `NTT⁻¹` (from 255 down).
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-! ## The zetas -/

/-- `ζ^BitRev8(m) mod q`, as a number. -/
def zetaNat (m : Nat) : Nat := 1753 ^ bitRev8 m % 8380417

theorem zetaNat_eq (m : Nat) : zetaNat m = (zetas m).val := by
  rw [zetas, val_pow]; rfl

theorem zetaNat_lt (m : Nat) : zetaNat m < q := Nat.mod_lt _ (by decide)

/-- `-ζ^BitRev8(m) mod q`, as a number: the zeta of `NTT⁻¹`. -/
def negZetaNat (m : Nat) : Nat := (8380417 - zetaNat m) % 8380417

theorem negZetaNat_eq (m : Nat) : negZetaNat m = (-zetas m).val := by
  rw [val_neg, ← zetaNat_eq]; rfl

theorem negZetaNat_lt (m : Nat) : negZetaNat m < q := Nat.mod_lt _ (by decide)

/-! ## Butterflies -/

/-- The butterfly of Algorithm 41 (lines 8–10) on `w[j]` and `w[j + len]`
with the zeta `z`: `t ← z · w[j + len]`, `w[j + len] ← w[j] - t`,
`w[j] ← w[j] + t`. -/
def bfly (w : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := z * w[j + len]!
  let w := w.set! (j + len) (w[j]! - t)
  w.set! j (w[j]! + t)

/-- The butterfly of Algorithm 42 (lines 8–11) on `w[j]` and `w[j + len]`
with the zeta `z`: `t ← w[j]`, `w[j] ← t + w[j + len]`,
`w[j + len] ← t - w[j + len]`, `w[j + len] ← z · w[j + len]`. -/
def bflyInv (w : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := w[j]!
  let w := w.set! j (t + w[j + len]!)
  let w := w.set! (j + len) (t - w[j + len]!)
  w.set! (j + len) (z * w[j + len]!)

/-- A butterfly changes `w[j]` to `w[j] + z·w[j + len]` and `w[j + len]` to
`w[j] - z·w[j + len]`, and nothing else. -/
theorem bfly_get (w : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bfly w j len z)[i]! =
      if i = j then w[j]! + z * w[j + len]!
      else if i = j + len then w[j]! - z * w[j + len]!
      else w[i]! := by
  simp only [bfly]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_self _ hi, getElem!_set!_ne _ hi (by omega), ite_eq_left rfl]
  · rw [getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), ite_eq_right h2]

/-- An inverse butterfly changes `w[j]` to `w[j] + w[j + len]` and
`w[j + len]` to `z·(w[j] - w[j + len])`, and nothing else. -/
theorem bflyInv_get (w : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bflyInv w j len z)[i]! =
      if i = j then w[j]! + w[j + len]!
      else if i = j + len then z * (w[j]! - w[j + len]!)
      else w[i]! := by
  simp only [bflyInv]
  rw [getElem!_set!_self _ hj, getElem!_set!_ne _ hj (by omega)]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_ne _ hi (by omega), getElem!_set!_ne _ hi (by omega), getElem!_set!_self _ hi,
      ite_eq_left rfl]
  · rw [ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), getElem!_set!_ne _ hi (Ne.symm h2),
        getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h2]

/-! ## Loops -/

theorem foldl_range'_succ {α : Type} (g : α → Nat → α) (x : α) (s t : Nat) :
    (List.range' s (t + 1)).foldl g x = g ((List.range' s t).foldl g x) (s + t) := by
  rw [List.range'_concat, List.foldl_append, Nat.one_mul]; rfl

theorem foldl_range_succ {α : Type} (g : α → Nat → α) (x : α) (t : Nat) :
    (List.range (t + 1)).foldl g x = g ((List.range t).foldl g x) t := by
  rw [List.range_succ, List.foldl_append]; rfl

/-- The first `t` iterations of the innermost loop for the block from
`start` of the layer with `len`: the butterflies `op` with the zeta `z`. -/
def blockN (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start t : Nat) : Poly :=
  (List.range' start t).foldl (fun w j => op w j len z) w

/-- The first `b` iterations of the middle loop for the layer with `len`:
blocks `0 … b - 1`, block `c` from `2 · len · c` with the zeta `zf c`. -/
def layerN (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (zf : Nat → Zq) (b : Nat) : Poly :=
  (List.range b).foldl (fun w c => blockN op w len (zf c) (2 * len * c) len) w

theorem blockN_zero (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start : Nat) :
    blockN op w len z start 0 = w := rfl

theorem blockN_succ (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start t : Nat) :
    blockN op w len z start (t + 1) = op (blockN op w len z start t) (start + t) len z :=
  foldl_range'_succ _ _ _ _

theorem layerN_zero (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (zf : Nat → Zq) :
    layerN op w len zf 0 = w := rfl

theorem layerN_succ (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (zf : Nat → Zq) (b : Nat) :
    layerN op w len zf (b + 1) = blockN op (layerN op w len zf b) len (zf b) (2 * len * b) len :=
  foldl_range_succ _ _ _

/-- Each coefficient after the first `t` butterflies of a block of `NTT`:
the butterflies on `(j, j + len)` for `start ≤ j < start + t` are done. -/
theorem blockN_bfly_get (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (blockN bfly w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + z * w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then w[i - len]! - z * w[i]!
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- Each coefficient after the first `t` inverse butterflies of a block of
`NTT⁻¹`. -/
theorem blockN_bflyInv_get (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (blockN bflyInv w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then z * (w[i - len]! - w[i]!)
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bflyInv_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-! ## NTT -/

/-- The values of `len` of the layers of Algorithm 41, in order. -/
def nttLens : List Nat := [128, 64, 32, 16, 8, 4, 2, 1]

/-- The middle loop of Algorithm 41: the `128 / len` blocks of the layer
with `len`, block `c` with the zeta `zetas (128 / len + c)`. -/
def nttLayer (w : Poly) (len : Nat) : Poly := layerN bfly w len (fun c => zetas (128 / len + c)) (128 / len)

/-- A step of the middle loop of Algorithm 41 with the counter `m`, as the
standard writes it. -/
private def nttMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (blockN bfly b.1 len (zetas (b.2 + 1)) start len, b.2 + 1)

/-- A step of the outer loop of Algorithm 41 with the counter `m`. -/
private def nttOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttMid len) b

private theorem ntt_eq_outer (w : Poly) : ntt w = (nttLens.foldl nttOuter (w, 0)).1 := by
  simp only [ntt, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  apply congrArg Prod.fst
  apply congrArg (List.foldl · _ _)
  funext b len
  unfold nttOuter
  rfl

private theorem foldl_nttMid (len st m : Nat) (w : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttMid len) (w, m) =
      ((List.range cnt).foldl (fun g c => blockN bfly g len (zetas (m + 1 + c)) (st * c) len) w, m + cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttMid len st m w cnt, foldl_range_succ,
      Nat.zero_add]
    show (blockN bfly _ len (zetas (m + cnt + 1)) (st * cnt) len, m + cnt + 1) = _
    rw [Nat.add_right_comm m cnt 1]
    exact Prod.ext rfl (by omega)

private theorem nttOuter_eq (w : Poly) (len m : Nat) :
    nttOuter (w, m) len = ((List.range (n / (2 * len))).foldl
      (fun g c => blockN bfly g len (zetas (m + 1 + c)) (2 * len * c) len) w, m + n / (2 * len)) :=
  foldl_nttMid _ _ _ _ _

/-- `NTT` is its eight layers, in order. -/
theorem ntt_eq_layers (w : Poly) : ntt w = nttLens.foldl nttLayer w := by
  rw [ntt_eq_outer]
  simp only [nttLens, List.foldl_cons, List.foldl_nil, nttOuter_eq, nttLayer, layerN, n,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd]

/-! ## NTT⁻¹ -/

/-- The values of `len` of the layers of Algorithm 42, in order. -/
def nttInvLens : List Nat := [1, 2, 4, 8, 16, 32, 64, 128]

/-- The middle loop of Algorithm 42: the `128 / len` blocks of the layer
with `len`, block `c` with the zeta `-zetas (256 / len - 1 - c)`. -/
def nttInvLayer (w : Poly) (len : Nat) : Poly :=
  layerN bflyInv w len (fun c => -zetas (256 / len - 1 - c)) (128 / len)

/-- A step of the middle loop of Algorithm 42 with the counter `m`, as the
standard writes it. -/
private def nttInvMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (blockN bflyInv b.1 len (-zetas (b.2 - 1)) start len, b.2 - 1)

/-- A step of the outer loop of Algorithm 42 with the counter `m`. -/
private def nttInvOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttInvMid len) b

private theorem nttInv_eq_outer (w : Poly) :
    nttInv w = ((nttInvLens.foldl nttInvOuter (w, 256)).1).map (· * 8347681) := by
  simp only [nttInv, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  apply congrArg (fun v => Vector.map _ (Prod.fst v))
  apply congrArg (List.foldl · _ _)
  funext b len
  unfold nttInvOuter
  rfl

private theorem foldl_nttInvMid (len st m : Nat) (w : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttInvMid len) (w, m) =
      ((List.range cnt).foldl (fun g c => blockN bflyInv g len (-zetas (m - 1 - c)) (st * c) len) w, m - cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttInvMid len st m w cnt, foldl_range_succ,
      Nat.zero_add]
    show (blockN bflyInv _ len (-zetas (m - cnt - 1)) (st * cnt) len, m - cnt - 1) = _
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm cnt 1]

private theorem nttInvOuter_eq (w : Poly) (len m : Nat) :
    nttInvOuter (w, m) len = ((List.range (n / (2 * len))).foldl
      (fun g c => blockN bflyInv g len (-zetas (m - 1 - c)) (2 * len * c) len) w, m - n / (2 * len)) :=
  foldl_nttInvMid _ _ _ _ _

/-- `NTT⁻¹` is its eight layers, in order, and the multiplication of every
coefficient by `8347681 = 256⁻¹ mod q`. -/
theorem nttInv_eq_layers (w : Poly) :
    nttInv w = (nttInvLens.foldl nttInvLayer w).map (· * 8347681) := by
  rw [nttInv_eq_outer]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil, nttInvOuter_eq, nttInvLayer,
    layerN, n, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]

end VG.Proof.MlDsa.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt`. -/
section

/-! Block identities shared by vector NTT implementations. -/
namespace VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)

/-- The first `t` butterflies of a block of the specification, with the
zeta of index `k` of the table, do `op` to `(j, j + len)`. -/
structure BlkOk (blk : Poly → Nat → Nat → Nat → Nat → Poly) (op : Zq → Zq → Zq → Zq × Zq) : Prop where
  zero : ∀ f len k st, blk f len k st 0 = f
  add : ∀ f len k st t t', blk f len k st (t + t') = blk (blk f len k st t) len k (st + t) t'
  get : ∀ f len k st t, 0 < len → t ≤ len → st + len + t ≤ n → ∀ i < n,
    (blk f len k st t)[i]! = if st ≤ i ∧ i < st + t then (op f[i]! f[i + len]! (zetas k)).1
      else if st + len ≤ i ∧ i < st + len + t then (op f[i - len]! f[i]! (zetas k)).2 else f[i]!

theorem blockN_add (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len : Nat) (z : Zq) (st t t' : Nat) :
    blockN op f len z st (t + t') = blockN op (blockN op f len z st t) len z (st + t) t' := by
  simp only [blockN]; rw [← List.foldl_append, List.range'_append_1]

/-- `blockN_bfly_get`, for the butterflies of the block up to `start + t`
only. -/
theorem blockN_bfly_get' (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (blockN bfly w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + z * w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then w[i - len]! - z * w[i]!
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- `blockN_bflyInv_get`, for the butterflies of the block up to
`start + t` only. -/
theorem blockN_bflyInv_get' (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (blockN bflyInv w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then z * (w[i - len]! - w[i]!)
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bflyInv_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

theorem nttBlk_ok : BlkOk (fun f len k st t => blockN bfly f len (zetas k) st t)
    (fun x y z => (x + z * y, x - z * y)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => blockN_bfly_get' f hl ht hs hi⟩

/-- Algorithm 42 multiplies by `-ζ`; `vibfly` by `ζ`, the other way round. -/
theorem neg_mul_sub (z x y : Zq) : -z * (x - y) = z * (y - x) := by
  grind

theorem nttInvBlk_ok : BlkOk (fun f len k st t => blockN bflyInv f len (-zetas k) st t)
    (fun x y z => (x + y, z * (y - x))) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => by rw [blockN_bflyInv_get' f hl ht hs hi, neg_mul_sub]⟩

/-- The first `b` blocks of the layer with `len`, block `c` with the zeta of
index `zi c`. -/
def layF (blk : Poly → Nat → Nat → Nat → Nat → Poly) (F : Poly) (len : Nat) (zi : Nat → Nat) (b : Nat) :
    Poly :=
  (List.range b).foldl (fun f c => blk f len (zi c) (2 * len * c) len) F

/-- Each coefficient after the first `b` blocks of the layer with `len = 1`. -/
theorem layF1_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op) (F : Poly) (zi : Nat → Nat) {b : Nat} (hb : b ≤ 128) {j : Nat} (hj : j < 256) :
    (layF blk F 1 zi b)[j]! = if j < 2 * b then
      (if j % 2 = 0 then (op F[j]! F[j + 1]! (zetas (zi (j / 2)))).1
        else (op F[j - 1]! F[j]! (zetas (zi (j / 2)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ 1 _ _ 1 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2 * 1 * b ≤ j ∧ j < 2 * 1 * b + 1
    · rw [ite_eq_left h1, ih (by omega) hj, ih (by omega) (by omega), show j / 2 = b by omega]
      simp (disch := omega) only [ite_eq_left, ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2 * 1 * b + 1 ≤ j ∧ j < 2 * 1 * b + 1 + 1
      · rw [ite_eq_left h2, ih (by omega) (by omega), ih (by omega) hj, show j / 2 = b by omega]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
      · rw [ite_eq_right h2, ih (by omega) hj]
        by_cases h3 : j < 2 * b <;> simp (disch := omega) only [ite_eq_left, ite_eq_right]


/-- Each coefficient after the first `b` blocks of a length-two layer. -/
theorem layF2_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op) (F : Poly) (zi : Nat → Nat)
    {b : Nat} (hb : b ≤ 64) {j : Nat} (hj : j < 256) :
    (layF blk F 2 zi b)[j]! = if j < 4*b then
      (if j%4 < 2 then (op F[j]! F[j+2]! (zetas (zi (j/4)))).1
       else (op F[j-2]! F[j]! (zetas (zi (j/4)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF,foldl_range_succ,← layF,
      hblk.get _ 2 _ _ 2 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2*2*b ≤ j ∧ j < 2*2*b+2
    · rw [ite_eq_left h1,ih (by omega) hj,ih (by omega) (by omega),show j/4 = b by omega]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2*2*b+2 ≤ j ∧ j < 2*2*b+2+2
      · rw [ite_eq_left h2,ih (by omega) (by omega),ih (by omega) hj,show j/4 = b by omega]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h2,ih (by omega) hj]
        by_cases h3 : j < 4*b <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]

end VG.Proof.MlDsa.Arith

end
