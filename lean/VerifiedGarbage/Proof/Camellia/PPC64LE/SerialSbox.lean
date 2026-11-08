module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.Serial
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.Serial
public import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Camellia.SboxTable
meta import VerifiedGarbage.Proof.Camellia.SboxTable
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia's S-boxes through the AES S-box, on all 256 inputs

The single-block core's S-boxes (`Impl/Camellia/PPC64LE/Serial.lean`) are
an affine map of an input's nibbles (`aff`), the AES S-box, and an affine
map of the output's: `A_in`'s tables (`inLo`, `inHi`) or those of
`A_in ∘ rotl 1` (`in4Lo`, `in4Hi`), and `A_out`'s (`outLo`, `outHi`) or
those of `rotl 1 ∘ A_out` (`out2…`) or `rotl 7 ∘ A_out` (`out3…`).
`sbox1_affine` … `sbox4_affine`: they are `SBOX1` … `SBOX4` on every byte.
The kernel evaluates the AES S-box of the 256 images of each input map at
once, on truth tables (`Proof.Aes.sboxT`, `midT`, `mid4T`, written out once
by `materialize_value`), then checks each input against `SBOX1`'s truth
tables (`Proof.Camellia.sbox1T`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.Serial

open VG VG.Bitslice
open VG.Impl.Camellia.PPC64LE.Serial

/-- An affine map on bytes, by the tables of its low and high nibbles. -/
def aff (lo hi : Vector Byte 16) (b : Byte) : Byte := lo.getD (b &&& 0x0f).toNat 0 ^^^ hi.getD (b >>> 4).toNat 0

/-- The truth tables of an affine map. -/
def affT (lo hi : Vector Byte 16) : List Nat :=
  (List.range 8).map fun j => tableOf (fun c => (aff lo hi (BitVec.ofNat 8 c)).getLsbD j) 256

/-- The AES S-box of `A_in`, and of `A_in ∘ rotl 1`, on all inputs. -/
def midT : List Nat := Proof.Aes.sboxT (affT inLo inHi)
def mid4T : List Nat := Proof.Aes.sboxT (affT in4Lo in4Hi)

/-- `SBOX1`'s truth tables. -/
def s1T : List Nat := (List.range 8).map Proof.Camellia.sbox1T

end VG.Proof.Camellia.PPC64LE.Serial

namespace VG

materialize_value Proof.Camellia.PPC64LE.Serial.midT
materialize_value Proof.Camellia.PPC64LE.Serial.mid4T

end VG

namespace VG.Proof.Camellia.PPC64LE.Serial

open VG VG.Bitslice
open VG.Impl.Camellia.PPC64LE.Serial

theorem affT_length (lo hi : Vector Byte 16) : (affT lo hi).length = 8 := by simp [affT]

theorem row_affT (lo hi : Vector Byte 16) {c : Nat} (hc : c < 256) :
    Proof.Aes.row (affT lo hi) c = aff lo hi (BitVec.ofNat 8 c) := by
  refine Proof.Aes.row_ext fun j hj => ?_
  simp only [affT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, testBit_tableOf, hc, decide_true, Bool.true_and]

theorem row_s1T {c : Nat} (hc : c < 256) : Proof.Aes.row s1T c = Spec.Camellia.sbox1 (BitVec.ofNat 8 c) := by
  refine Proof.Aes.row_ext fun j hj => ?_
  simp only [s1T, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  exact Proof.Camellia.testBit_sbox1T hc

/-! ## The checks, on the tables written out -/

theorem check1 : ∀ c < 256, (aff outLo outHi (Proof.Aes.row midT c)).toNat = (Proof.Aes.row s1T c).toNat := by
  lit_decide
theorem check4 : ∀ c < 256, (aff outLo outHi (Proof.Aes.row mid4T c)).toNat =
    (Proof.Aes.row s1T ((BitVec.ofNat 8 c).rotateLeft 1).toNat).toNat := by
  lit_decide
theorem check2 : ∀ c < 256, (aff out2Lo out2Hi (Proof.Aes.row midT c)).toNat =
    ((Proof.Aes.row s1T c).rotateLeft 1).toNat := by
  lit_decide
theorem check3 : ∀ c < 256, (aff out3Lo out3Hi (Proof.Aes.row midT c)).toNat =
    ((Proof.Aes.row s1T c).rotateLeft 7).toNat := by
  lit_decide

/-! ## The S-boxes -/

theorem mid_eq (b : Byte) : Proof.Aes.row midT b.toNat = Spec.Aes.sbox (aff inLo inHi b) := by
  rw [midT, Proof.Aes.row_sboxT (affT_length _ _) b.isLt, row_affT _ _ b.isLt, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem mid4_eq (b : Byte) : Proof.Aes.row mid4T b.toNat = Spec.Aes.sbox (aff in4Lo in4Hi b) := by
  rw [mid4T, Proof.Aes.row_sboxT (affT_length _ _) b.isLt, row_affT _ _ b.isLt, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem s1_eq (b : Byte) : Proof.Aes.row s1T b.toNat = Spec.Camellia.sbox1 b := by
  rw [row_s1T b.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem sbox1_affine (b : Byte) :
    aff outLo outHi (Spec.Aes.sbox (aff inLo inHi b)) = Spec.Camellia.sbox1 b := by
  have e := check1 b.toNat b.isLt
  rw [mid_eq, s1_eq] at e
  exact BitVec.eq_of_toNat_eq e

theorem sbox4_affine (b : Byte) :
    aff outLo outHi (Spec.Aes.sbox (aff in4Lo in4Hi b)) = Spec.Camellia.sbox4 b := by
  have e := check4 b.toNat b.isLt
  rw [mid4_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq, s1_eq] at e
  exact BitVec.eq_of_toNat_eq e

theorem sbox2_affine (b : Byte) :
    aff out2Lo out2Hi (Spec.Aes.sbox (aff inLo inHi b)) = Spec.Camellia.sbox2 b := by
  have e := check2 b.toNat b.isLt
  rw [mid_eq, s1_eq] at e
  exact BitVec.eq_of_toNat_eq e

theorem sbox3_affine (b : Byte) :
    aff out3Lo out3Hi (Spec.Aes.sbox (aff inLo inHi b)) = Spec.Camellia.sbox3 b := by
  have e := check3 b.toNat b.isLt
  rw [mid_eq, s1_eq] at e
  exact BitVec.eq_of_toNat_eq e

end VG.Proof.Camellia.PPC64LE.Serial
