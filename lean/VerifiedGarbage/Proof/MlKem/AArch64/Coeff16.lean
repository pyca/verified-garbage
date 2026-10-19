module

import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.Mem16Bytes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# ML-KEM on AArch64: polynomials stored with 16-bit coefficients

A 16-bit coefficient from its two bytes (`coeffAtW16_toNat`) and from a
halfword of a vector loaded from memory (`vhalf_read_coeff`); the bytes of
coefficients `F` stored with 16 bits (`bytesW16`), written a vector of eight
halfwords at a time (`halves_bytes`, `BytesUpTo.writeN`), and the polynomial
they store (`polyIsW16_of_bytes`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem

/-- Halfword `e` of a vector read from memory, from its two bytes. -/
theorem vhalf_read_toNat (m : Mem) (a : Addr) {e : Nat} (he : e < 8) :
    (vhalf (m.read a 16) e).toNat =
      (m (a + BitVec.ofNat 64 (2 * e))).toNat + 256 * (m (a + BitVec.ofNat 64 (2 * e + 1))).toNat := by
  rw [Cbd16.half_bytes, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _),
    Nat.shiftLeft_eq, vbyte, vbyte, Mem.extractLsb'_read m a (by omega),
    Mem.extractLsb'_read m a (by omega)]
  omega

/-- Halfword `e` of the vector at coefficient `j` of a polynomial stored with 16 bits. -/
theorem vhalf_read_coeff (m : Mem) (p : Addr) (j : Nat) {e : Nat} (he : e < 8) :
    (vhalf (m.read (p + BitVec.ofNat 64 (2 * j)) 16) e).toNat = (coeffAtW 16 m p (j + e)).toNat := by
  rw [vhalf_read_toNat _ _ he, coeffAtW16_toNat, ptr_add, ptr_add, show 2 * j + 2 * e = 2 * (j + e) by omega,
    show 2 * j + (2 * e + 1) = 2 * (j + e) + 1 by omega]

/-- A byte of a vector, from its halfwords. -/
theorem vbyte_of_vhalf (x : BitVec 128) (i : Nat) :
    (vbyte x i).toNat = (vhalf x (i / 2)).toNat / 256 ^ (i % 2) % 256 := by
  have hl := (vbyte x (2 * (i / 2))).isLt
  have hh := (vbyte x (2 * (i / 2) + 1)).isLt
  rw [Cbd16.half_bytes, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _),
    Nat.shiftLeft_eq]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, show 2 * (i / 2) = i by omega]
    simp only [Nat.pow_zero, Nat.div_one]
    omega
  · rw [h, show 2 * (i / 2) + 1 = i by omega]
    simp only [Nat.pow_one]
    omega

/-- A vector of the eight coefficients `F (t + e)` is the bytes from `2 t`. -/
theorem halves_bytes {x : BitVec 128} {F : Nat → Nat} {t : Nat} (hx : ∀ e < 8, (vhalf x e).toNat = F (t + e)) :
    ∀ i < 16, x.extractLsb' (8 * i) 8 = bytesW16 F (2 * t + i) := fun i hi => by
  apply BitVec.eq_of_toNat_eq
  rw [show x.extractLsb' (8 * i) 8 = vbyte x i from rfl, vbyte_of_vhalf x i, hx _ (by omega), bytesW16,
    BitVec.toNat_ofNat, show (2 * t + i) / 2 = t + i / 2 by omega, show (2 * t + i) % 2 = i % 2 by omega]

/-- `n` bytes `x` stored at byte `t` of `N`. -/
theorem BytesUpTo.writeN {m : Mem} {p : Addr} {N t n : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p N t L old) (hN : N < 2 ^ 32) (hn : t + n ≤ N) {x : BitVec (8 * n)}
    (hx : ∀ i < n, x.extractLsb' (8 * i) 8 = L (t + i)) :
    BytesUpTo (m.write (p + BitVec.ofNat 64 t) n x) p N (t + n) L old := by
  intro j hj
  have d : ((p + BitVec.ofNat 64 j) - (p + BitVec.ofNat 64 t)).toNat =
      if t ≤ j then j - t else 2 ^ 64 + j - t :=
    Offset.sub_toNat' p (by omega) (by omega)
  rw [Mem.write, d]
  by_cases ht : t ≤ j
  · rw [ite_eq_left ht]
    by_cases hnj : j - t < n
    · rw [ite_eq_left hnj, ite_eq_left (by omega), hx _ hnj]
      congr 1; omega
    · rw [ite_eq_right hnj, h j hj, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right ht, ite_eq_right (by omega), h j hj, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- All bytes of a polynomial written: the polynomial, stored with 16 bits. -/
theorem polyIsW16_of_bytes' {m : Mem} {p : Addr} {f : Poly} {old : Nat → Byte}
    (h : BytesUpTo m p 512 512 (bytesW16 fun i => (f[i]!).val) old) : PolyIsW 16 m p f :=
  polyIsW16_of_bytes fun j hj => by rw [h j hj, ite_eq_left hj]

/-- A byte of the polynomial at `p` after a vector is stored at byte `2 t` of it. -/
theorem write16_byte (m : Mem) (p : Addr) {t j : Nat} (ht : 2 * t + 16 ≤ 512) (hj : j < 512)
    (x : BitVec 128) :
    m.write (p + BitVec.ofNat 64 (2 * t)) 16 x (p + BitVec.ofNat 64 j) =
      if 2 * t ≤ j ∧ j < 2 * t + 16 then vbyte x (j - 2 * t) else m (p + BitVec.ofNat 64 j) := by
  rw [Mem.write, Offset.sub_toNat' p (by omega) (by omega)]
  by_cases c : 2 * t ≤ j
  · rw [ite_eq_left c]
    by_cases c' : j - 2 * t < 16
    · rw [ite_eq_left c', ite_eq_left ⟨c, by omega⟩]; rfl
    · rw [ite_eq_right c', ite_eq_right (by omega)]
  · rw [ite_eq_right c, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A 16-bit coefficient after a vector of eight is stored at coefficient `t`. -/
theorem coeffAtW16_write (m : Mem) (p : Addr) {t i : Nat} (ht : t + 8 ≤ 256) (hi : i < 256)
    (x : BitVec 128) :
    coeffAtW 16 (m.write (p + BitVec.ofNat 64 (2 * t)) 16 x) p i =
      if t ≤ i ∧ i < t + 8 then vhalf x (i - t) else coeffAtW 16 m p i := by
  apply BitVec.eq_of_toNat_eq
  rw [coeffAtW16_toNat, write16_byte m p (by omega) (by omega), write16_byte m p (by omega) (by omega)]
  by_cases c : t ≤ i ∧ i < t + 8
  · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩, ite_eq_left c,
      Cbd16.half_bytes, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _),
      Nat.shiftLeft_eq, show 2 * i - 2 * t = 2 * (i - t) by omega,
      show 2 * i + 1 - 2 * t = 2 * (i - t) + 1 by omega]
    omega
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right c, coeffAtW16_toNat]

/-- The coefficients `i ∈ S` of the polynomial stored with 16 bits at `p` are `G i`, the others
`old i`. -/
def CoeffsInW (m : Mem) (p : Addr) (S : Nat → Prop) [DecidablePred S] (G old : Nat → BitVec 16) :
    Prop :=
  ∀ i < 256, coeffAtW 16 m p i = if S i then G i else old i

theorem CoeffsInW.congr {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S] [DecidablePred S']
    {G old : Nat → BitVec 16} (h : CoeffsInW m p S G old) (hS : ∀ i < 256, (S' i ↔ S i)) :
    CoeffsInW m p S' G old := fun i hi => by
  rw [h i hi]
  by_cases c : S i
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 c)]
  · rw [ite_eq_right c, ite_eq_right (fun h' => c ((hS i hi).1 h'))]

/-- Storing the eight coefficients `t, …, t + 7`. -/
theorem CoeffsInW.write16 {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S]
    [DecidablePred S'] {G old : Nat → BitVec 16} (h : CoeffsInW m p S G old) {t : Nat} (ht : t + 8 ≤ 256)
    {x : BitVec 128} (hx : ∀ e < 8, vhalf x e = G (t + e))
    (hS : ∀ i < 256, (S' i ↔ S i ∨ (t ≤ i ∧ i < t + 8))) :
    CoeffsInW (m.write (p + BitVec.ofNat 64 (2 * t)) 16 x) p S' G old := fun i hi => by
  rw [coeffAtW16_write _ _ ht hi, h i hi]
  by_cases c : t ≤ i ∧ i < t + 8
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 (Or.inr c)), hx _ (by omega),
      show t + (i - t) = i by omega]
  · rw [ite_eq_right c]
    by_cases c' : S i
    · rw [ite_eq_left c', ite_eq_left ((hS i hi).2 (Or.inl c'))]
    · rw [ite_eq_right c', ite_eq_right (fun h' => ((hS i hi).1 h').elim c' c)]

/-- All coefficients written: the polynomial, stored with 16 bits. -/
theorem CoeffsInW.polyIs {m : Mem} {p : Addr} {S : Nat → Prop} [DecidablePred S] {G old : Nat → BitVec 16}
    (h : CoeffsInW m p S G old) (hS : ∀ i < 256, S i) {f : Poly}
    (hG : ∀ i < 256, (G i).toNat = (f[i]!).val) : PolyIsW 16 m p f := by
  have hc : ∀ i < n, (coeffAtW 16 m p i).toNat = (f[i]!).val := fun i hi => by
    rw [h i hi, ite_eq_left (hS i hi), hG i hi]
  refine ⟨fun i hi => by rw [hc i hi]; exact Fin.isLt _, ext_getElem! fun i hi => ?_⟩
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]
  rw [hc i hi, ofNat_val]

end VG.Proof.MlKem.AArch64
