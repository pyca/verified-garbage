module

public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.CoeffW
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Impl.MlKem.AArch64.Sample
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on AArch64: the coefficients `SampleNTT`'s loop stores

The coefficients the loop of `SampleNTT` has accepted, as it stores them:
32 bits apart, or with `w16` 16 bits apart (`cvW`). Appending one
(`cvW_append`, `cvW_last`), the comparison with `q` that accepts a candidate
(`lt_q_arith`), and the polynomial they are, which is reduced (`cv_toPoly`,
`reduced_of_coeffs`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- Coefficient `i` of the list `L`, as stored. -/
def cvW (w16 : Bool) (L : List Zq) (i : Nat) : BitVec (cw w16) := BitVec.ofNat (cw w16) (L.getD i 0).val

theorem cvW_append {w16 : Bool} (L : List Zq) (x : Zq) {i : Nat} (hi : i < L.length) :
    cvW w16 L i = cvW w16 (L ++ [x]) i := by
  simp only [cvW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem cvW_last {w16 : Bool} (L : List Zq) (x : Zq) :
    cvW w16 (L ++ [x]) L.length = BitVec.ofNat (cw w16) x.val := by
  simp [cvW]

/-- `v - q`, negative exactly when `v < q`. -/
theorem lt_q_arith {a b : BitVec 64} {v : Nat} (ha : a.toNat = v) (hv : v < 2 ^ 12)
    (hb : b.toNat = q) : ((a - b) >>> 63).toNat = if v < q then 1 else 0 := by
  rw [toNat_lsr, BitVec.toNat_sub, ha, hb]
  have hq : q = 3329 := rfl
  split <;> omega_arith

/-! ## The loop -/

theorem cv_toPoly {w16 : Bool} {L : List Zq} {i : Nat} (hi : i < 256) :
    cvW w16 L i = BitVec.ofNat (cw w16) ((toPoly L)[i]!).val := by
  simp [cvW, toPoly, hi]

theorem reduced_of_coeffs {w16 : Bool} {m : Mem} {p : Addr} {L : List Zq}
    (h : CoeffsUpToW w16 m p L.length (cvW w16 L) fun _ => 0) : ReducedW (cw w16) m p := fun i hi => by
  rw [h i hi]
  split
  · simp only [cvW, BitVec.toNat_ofNat]
    have := val_lt (L.getD i 0)
    have hq : q = 3329 := rfl
    cases w16 <;> simp only [cw, Bool.false_eq_true, ite_false, ite_true] <;> omega_arith
  · show (0 : BitVec (cw w16)).toNat < q
    exact Nat.lt_of_le_of_lt (Nat.le_of_eq (by cases w16 <;> rfl)) (by decide : 0 < q)

end VG.Proof.MlKem.AArch64.Sample
