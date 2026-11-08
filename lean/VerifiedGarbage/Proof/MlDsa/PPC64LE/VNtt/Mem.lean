module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Lanes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # ML-DSA's vector NTT on PPC64LE: vectors of coefficients in memory

`lxvd2x` puts the word at `a + 4·(e XOR 1)` in lane `e` (`vword_load`), and
`stxvd2x` writes lane `e` there (`readW_store`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE

/-- Bit `i` of a little-endian read is bit `i % 8` of byte `i / 8`. -/
theorem getLsbD_read (m : Mem) (a : Addr) {n i : Nat} (hi : i < 8 * n) :
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  have h := congrArg (BitVec.getLsbD · (i % 8)) (Mem.extractLsb'_read m a (n := n) (j := i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and] at h
  rw [← h]
  exact congrArg _ (by omega)

/-- Bytes `k … k + l` of a read. -/
theorem read_extract (m : Mem) (a : Addr) {n k l : Nat} (h : k + l ≤ n) :
    (m.read a n).extractLsb' (8 * k) (8 * l) = m.read (a + BitVec.ofNat 64 k) l := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and, getLsbD_read _ _ (by omega),
    getLsbD_read _ _ hr, BitVec.add_assoc, ← BitVec.ofNat_add, show (8 * k + r) / 8 = k + r / 8 by omega,
    show (8 * k + r) % 8 = r % 8 by omega]


theorem getLsbD_swap (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (swapDwords x).getLsbD p = x.getLsbD (if p < 64 then p + 64 else p - 64) := by
  simp only [swapDwords, vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : p < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]; exact congrArg _ (by omega)
  · simp only [h, ite_false, show p - 64 < 64 by omega, decide_true, Bool.true_and]; exact congrArg _ (by omega)

theorem xor1_lt {e : Nat} (he : e < 4) : e ^^^ 1 < 4 := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> decide

/-- Lane `e` of `swapDwords x` is word `e XOR 1` of `x` from its low end. -/
theorem vword_swap (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (swapDwords x) e = x.extractLsb' (32 * (e ^^^ 1)) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vword, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  rw [getLsbD_swap _ (by omega)]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.reduceXor]
    split <;> first | omega | exact congrArg _ (by omega)

/-- Lane `e` of a `lxvd2x` of `[a, a + 16)`. -/
theorem vword_load (m : Mem) (a : Addr) {e : Nat} (he : e < 4) :
    vword (swapDwords (m.read a 16)) e = m.readW (a + BitVec.ofNat 64 (4 * (e ^^^ 1))) 32 := by
  have hk := xor1_lt he
  rw [vword_swap _ he, show 32 * (e ^^^ 1) = 8 * (4 * (e ^^^ 1)) by omega,
    read_extract m a (n := 16) (k := 4 * (e ^^^ 1)) (l := 4) (by omega)]
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- The word at `a + 4k` after a `stxvd2x` of `v` to `[a, a + 16)`. -/
theorem readW_store (m : Mem) (a : Addr) (v : BitVec 128) {k : Nat} (hk : k < 4) :
    (m.write a 16 (swapDwords v)).readW (a + BitVec.ofNat 64 (4 * k)) 32 = vword v (k ^^^ 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [Mem.readW, BitVec.setWidth_eq]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.write]
  rw [show a + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (r / 8) - a = BitVec.ofNat 64 (4 * k + r / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 4 * k + r / 8 < 16 by omega, ite_true, BitVec.getLsbD_extractLsb', show r % 8 < 8 by omega,
    decide_true, Bool.true_and, vword, hr]
  rw [getLsbD_swap _ (by omega)]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.reduceXor]
    split <;> first | omega | exact congrArg _ (by omega)

/-! ## Coefficients -/

open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add coeffAt_eq polyRegion polyIs_of_toNat polyIs_toNat)
open VG.Spec.MlDsa (Poly n)

/-- Lane `e` of a load of coefficients `j … j+3`. -/
theorem vword_loadC (m : Mem) (p : Addr) (j : Nat) {e : Nat} (he : e < 4) :
    vword (swapDwords (m.read (coeffAddr p j) 16)) e = coeffAt m p (j + (e ^^^ 1)) := by
  rw [vword_load _ _ he, coeffAddr_add, ← coeffAt_eq]

/-- Coefficient `i` after a store of `v` to coefficients `j … j+3`. -/
theorem coeffAt_store (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (v : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.write (coeffAddr p j) 16 (swapDwords v)) p i =
      if j ≤ i ∧ i < j + 4 then vword v ((i - j) ^^^ 1) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega]]
    exact readW_store _ _ _ (by omega)
  · have hw : m.write (coeffAddr p j) 16 (swapDwords v) = m.writeW (coeffAddr p j) (swapDwords v) := by
      simp only [Mem.writeW, BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem xor1_xor1 (e : Nat) : (e ^^^ 1) ^^^ 1 = e := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem vector_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) :
    (polyRegion p).Contains (coeffAddr p j) 16 := Offset.contains_base p (by omega) (by omega)

theorem frame_store2 {m m' : Mem} {p : Addr} (hf : Frame [polyRegion p] m m') {j j' : Nat}
    (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) (x y : BitVec 128) :
    Frame [polyRegion p] m ((m'.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) :=
  (hf.write (List.mem_singleton_self _) x (vector_contains p hj)).write
    (List.mem_singleton_self _) y (vector_contains p hj')

/-- Two stores of vectors of coefficients, at `j` and at `j'`. -/
theorem polyIs_store2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P)
    {j j' : Nat} (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256)
    {x y : BitVec 128} (hx : ∀ e < 4, (vword x e).toNat = (R[j + (e ^^^ 1)]!).val)
    (hy : ∀ e < 4, (vword y e).toNat = (R[j' + (e ^^^ 1)]!).val)
    (hR : ∀ i < 256, ¬(j ≤ i ∧ i < j + 4) → ¬(j' ≤ i ∧ i < j' + 4) → R[i]! = P[i]!) :
    PolyIs ((m.write (coeffAddr p j) 16 (swapDwords x)).write (coeffAddr p j') 16 (swapDwords y)) p R :=
  polyIs_of_toNat fun i hi => by
    have hi' : i < 256 := hi
    rw [coeffAt_store _ _ hj' _ hi', coeffAt_store _ _ hj _ hi']
    by_cases h1 : j' ≤ i ∧ i < j' + 4
    · rw [ite_eq_left h1, hy _ (xor1_lt (by omega)), xor1_xor1, show j' + (i - j') = i by omega]
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j + 4
      · rw [ite_eq_left h2, hx _ (xor1_lt (by omega)), xor1_xor1, show j + (i - j) = i by omega]
      · rw [ite_eq_right h2, hR i hi' h2 h1, polyIs_toNat hP hi]

end VG.Proof.MlDsa.PPC64LE.VNtt
