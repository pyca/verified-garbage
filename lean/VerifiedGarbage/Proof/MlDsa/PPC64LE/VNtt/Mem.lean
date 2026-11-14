module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Lanes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # ML-DSA's vector NTT on PPC64LE: vectors of coefficients in memory

Coefficients `j … j+3` loaded by `lxvd2x` (`vword_loadC`) and stored by
`stxvd2x` (`coeffAt_store`), from the order of `vword_load` and
`readW_store` (`Proof/Framework/PPC64LE/VWords.lean`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE

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
      rw [coeffAddr_add, show j + (i - j) = i by omega_using [h]]]
    exact readW_store _ _ _ (by omega_using [h])
  · have hw : m.write (coeffAddr p j) 16 (swapDwords v) = m.writeW (coeffAddr p j) (swapDwords v) := by
      simp only [Mem.writeW, BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_using [hi]) (by omega_using [hj])) (by decide)

theorem vector_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) :
    (polyRegion p).Contains (coeffAddr p j) 16 := Offset.contains_base p (by omega_using [hj]) (by omega_using [hj])

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
    · rw [ite_eq_left h1, hy _ (xor1_lt (by omega_using [h1])), xor1_xor1, show j' + (i - j') = i by omega_using [h1]]
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j + 4
      · rw [ite_eq_left h2, hx _ (xor1_lt (by omega_using [h2])), xor1_xor1, show j + (i - j) = i by omega_using [h2]]
      · rw [ite_eq_right h2, hR i hi' h2 h1, polyIs_toNat hP hi]

end VG.Proof.MlDsa.PPC64LE.VNtt
