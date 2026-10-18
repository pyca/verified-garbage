module

public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.Mem16Bytes

/-!
# ML-KEM: coefficients stored with 16 or 32 bits

The sampler stores a polynomial with 16-bit coefficients (`w16`) or 32-bit
ones, the same code but for the distance between coefficients (`cs w16`).
Coefficient `i`, as a number (`cval`), and how a 32-bit store of a value
less than `2¹⁶` at coefficient `j` changes it (`cval_writeW`): with 16 bits,
the store's upper half sets coefficient `j + 1` to zero.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.Spec.MlKem

/-- The bits of a coefficient: 16 with `w16`, otherwise 32. -/
abbrev cw (w16 : Bool) : Nat := if w16 then 16 else 32

/-- The bytes from a coefficient to the next. -/
abbrev cs (w16 : Bool) : Nat := if w16 then 2 else 4

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev cAddr (w16 : Bool) (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (cs w16 * i)

/-- Coefficient `i` of the polynomial at `p`, as a number. -/
def cval (w16 : Bool) (m : Mem) (p : Addr) (i : Nat) : Nat := (coeffAtW (cw w16) m p i).toNat

theorem cval_false (m : Mem) (p : Addr) (i : Nat) : cval false m p i = (coeffAt m p i).toNat := rfl

theorem cval_true (m : Mem) (p : Addr) (i : Nat) : cval true m p i = (coeffAtW 16 m p i).toNat := rfl

theorem cAddr_false (p : Addr) (i : Nat) : cAddr false p i = coeffAddr p i := rfl

/-- A 32-bit store at coefficient `i` stays in the 1024-byte slot of a polynomial. -/
theorem cs_store_le (w16 : Bool) {i : Nat} (hi : i < 256) : cs w16 * i + 4 ≤ 1024 := by
  cases w16 <;> simp only [cs, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem cAddr_add (w16 : Bool) (p : Addr) (j k : Nat) :
    cAddr w16 p j + BitVec.ofNat 64 (cs w16 * k) = cAddr w16 p (j + k) := by
  simp only [cAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

/-- A byte at `p + k` after a 32-bit store at `p + o`. -/
theorem writeW32_byte (m : Mem) (p : Addr) {o k : Nat} (ho : o + 4 ≤ 2 ^ 32) (hk : k < 2 ^ 32)
    (v : BitVec 32) :
    m.writeW (p + BitVec.ofNat 64 o) v (p + BitVec.ofNat 64 k) =
      if o ≤ k ∧ k < o + 4 then BitVec.ofNat 8 (v.toNat / 2 ^ (8 * (k - o))) else m (p + BitVec.ofNat 64 k) := by
  rw [Mem.writeW, Mem.write, Offset.sub_toNat' p (by omega) (by omega)]
  by_cases c : o ≤ k
  · rw [ite_eq_left c]
    by_cases c' : k - o < 32 / 8
    · rw [ite_eq_left c', ite_eq_left ⟨c, by omega⟩]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ (8 * (32 / 8)) from v.isLt)]
    · rw [ite_eq_right c', ite_eq_right (by omega)]
  · rw [ite_eq_right c, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A 32-bit store of `v < 2¹⁶` at coefficient `j`: coefficient `j` is `v`, and with 16-bit
coefficients `j + 1` is zero. -/
theorem cval_writeW {w16 : Bool} (m : Mem) (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256)
    (v : BitVec 32) (hv : v.toNat < 2 ^ 16) :
    cval w16 (m.writeW (cAddr w16 p j) v) p i =
      if i = j then v.toNat else if w16 = true ∧ i = j + 1 then 0 else cval w16 m p i := by
  cases w16
  · rw [cval_false, cval_false, cAddr_false, coeffAt_writeW m p (show i < n from hi) (show j < n from hj)]
    by_cases e : i = j
    · subst e; simp
    · rw [ite_eq_right (Ne.symm e), ite_eq_right e, ite_eq_right (by simp)]
  · rw [cval_true, cval_true, coeffAtW16_toNat, coeffAtW16_toNat]
    simp only [cAddr, cs, ite_true]
    rw [writeW32_byte m p (by omega) (by omega), writeW32_byte m p (by omega) (by omega)]
    by_cases e : i = j
    · subst e
      rw [ite_eq_left (show 2 * i ≤ 2 * i ∧ 2 * i < 2 * i + 4 by omega),
        ite_eq_left (show 2 * i ≤ 2 * i + 1 ∧ 2 * i + 1 < 2 * i + 4 by omega), ite_eq_left rfl,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, show 2 * i + 1 - 2 * i = 1 by omega, Nat.sub_self]
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]
      omega
    · rw [ite_eq_right e]
      by_cases e' : i = j + 1
      · subst e'
        rw [ite_eq_left (show 2 * j ≤ 2 * (j + 1) ∧ 2 * (j + 1) < 2 * j + 4 by omega),
          ite_eq_left (show 2 * j ≤ 2 * (j + 1) + 1 ∧ 2 * (j + 1) + 1 < 2 * j + 4 by omega),
          ite_eq_left ⟨trivial, rfl⟩, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show 2 * (j + 1) - 2 * j = 2 by omega, show 2 * (j + 1) + 1 - 2 * j = 3 by omega]
        have : v.toNat / 2 ^ 16 = 0 := Nat.div_eq_of_lt hv
        have : v.toNat / 2 ^ (8 * 3) = 0 := Nat.div_eq_of_lt (by omega)
        omega
      · simp only [e', and_false, ite_false]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The same store, as the `cw w16`-bit coefficient. -/
theorem coeffAtW_writeW {w16 : Bool} (m : Mem) (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256)
    (v : BitVec 32) (hv : v.toNat < 2 ^ 16) :
    coeffAtW (cw w16) (m.writeW (cAddr w16 p j) v) p i =
      if j = i then BitVec.ofNat (cw w16) v.toNat
      else if w16 = true ∧ i = j + 1 then 0 else coeffAtW (cw w16) m p i := by
  apply BitVec.eq_of_toNat_eq
  have h := cval_writeW (w16 := w16) m p hi hj v hv
  simp only [cval] at h
  rw [h]
  by_cases e : i = j
  · subst e
    rw [ite_eq_left rfl, ite_eq_left rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := v.isLt
    cases w16 <;> simp only [cw, Bool.false_eq_true, ite_false, ite_true] <;> omega
  · rw [ite_eq_right e, ite_eq_right (Ne.symm e)]
    split <;> simp

/-- A 32-bit store at a coefficient stays in the polynomial's 1024 bytes. -/
theorem cAddr_contains (w16 : Bool) (p : Addr) {i : Nat} (hi : i < 256) :
    (polyRegion p).Contains (cAddr w16 p i) 4 := by
  cases w16
  · exact coeff_contains p (show i < n from hi)
  · show (polyRegion p).Contains (p + BitVec.ofNat 64 (2 * i)) 4
    exact Offset.contains_base p (by omega) (by omega)

/-- A coefficient of a polynomial in a region the frame does not write. -/
theorem coeffAtW_frame {w16 : Bool} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAtW (cw w16) m' p i = coeffAtW (cw w16) m p i := by
  cases w16
  · show coeffAtW 32 m' p i = coeffAtW 32 m p i
    exact hf.readW (r := polyRegion p) (Offset.contains_base p (by omega) (by omega)) hd (by decide)
  · show coeffAtW 16 m' p i = coeffAtW 16 m p i
    exact hf.readW (r := polyRegion p) (Offset.contains_base p (by omega) (by omega)) hd (by decide)

/-- A polynomial in a region the frame does not write. -/
theorem polyAtW_frame {w16 : Bool} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) : polyAtW (cw w16) m' p = polyAtW (cw w16) m p := by
  simp only [polyAtW]
  exact Vector.ext fun i hi => by simp only [Vector.getElem_ofFn, coeffAtW_frame hf hd hi]

theorem reducedW_frame {w16 : Bool} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) (hr : ReducedW (cw w16) m p) : ReducedW (cw w16) m' p :=
  fun i hi => by rw [coeffAtW_frame hf hd hi]; exact hr i hi

theorem polyIsW_frame {w16 : Bool} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    {f : Poly} (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) (h : PolyIsW (cw w16) m p f) :
    PolyIsW (cw w16) m' p f :=
  ⟨reducedW_frame hf hd h.1, by rw [polyAtW_frame hf hd]; exact h.2⟩

/-- The coefficients at `p`: the first `t` of them are `G`'s, the others `old`'s. -/
def CoeffsUpToW (w16 : Bool) (m : Mem) (p : Addr) (t : Nat) (G old : Nat → BitVec (cw w16)) : Prop :=
  ∀ i < 256, coeffAtW (cw w16) m p i = if i < t then G i else old i

/-- `f` is stored with `w` bits at `p` if each coefficient is. -/
theorem polyIsW_of_toNat {w : Nat} {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAtW w m p i).toNat = (f[i]!).val) : PolyIsW w m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, ext_getElem! fun i hi => ?_⟩
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]
  rw [h i hi, ofNat_val]

/-- All 256 coefficients written. -/
theorem CoeffsUpToW.polyIs {w16 : Bool} {m : Mem} {p : Addr} {G old : Nat → BitVec (cw w16)}
    (h : CoeffsUpToW w16 m p 256 G old) {f : Poly}
    (hf : ∀ i < 256, G i = BitVec.ofNat (cw w16) (f[i]!).val) : PolyIsW (cw w16) m p f :=
  polyIsW_of_toNat fun i hi => by
    have hi' : i < 256 := hi
    rw [h i hi', ite_eq_left hi', hf i hi', BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := val_lt f[i]!
    have hq : q = 3329 := rfl
    cases w16 <;> simp only [cw, Bool.false_eq_true, ite_false, ite_true] <;> omega

end VG.Proof.MlKem
