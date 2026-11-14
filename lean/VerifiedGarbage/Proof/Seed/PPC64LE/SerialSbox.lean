module

public import VerifiedGarbage.Impl.Seed.PPC64LE.Serial
meta import VerifiedGarbage.Impl.Seed.PPC64LE.Serial
public import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Seed.Sbox
meta import VerifiedGarbage.Proof.Seed.Sbox
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED's S-boxes through the AES S-box, on all 256 inputs

The single-block core's S-boxes (`Impl/Seed/PPC64LE/Serial.lean`) are an
affine map of an input's nibbles (`aff`, by `inLo` and `inHi`), the AES
S-box, and an affine map of the output's (`out0…` or `out1…`).
`s0_affine`, `s1_affine`: they are `S1` and `S2` (`Spec.Seed.s0`, `s1`) on
every byte. The kernel evaluates the AES S-box of the 256 images of the input
map at once, on truth tables (`Proof.Aes.sboxT`, `midT`, written out once by
`materialize_value`), then checks each input against the S-boxes' truth
tables (`Proof.Seed.tableT`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Serial

open VG VG.Bitslice
open VG.Impl.Seed.PPC64LE.Serial

/-- An affine map on bytes, by the tables of its low and high nibbles. -/
def aff (lo hi : Vector Byte 16) (b : Byte) : Byte := lo.getD (b &&& 0x0f).toNat 0 ^^^ hi.getD (b >>> 4).toNat 0

/-- The truth tables of an affine map. -/
def affT (lo hi : Vector Byte 16) : List Nat :=
  (List.range 8).map fun j => tableOf (fun c => (aff lo hi (BitVec.ofNat 8 c)).getLsbD j) 256

/-- The AES S-box of `A_in`, on all inputs. -/
def midT : List Nat := Proof.Aes.sboxT (affT inLo inHi)

end VG.Proof.Seed.PPC64LE.Serial

namespace VG

materialize_value Proof.Seed.PPC64LE.Serial.midT

end VG

namespace VG.Proof.Seed.PPC64LE.Serial

open VG VG.Bitslice
open VG.Impl.Seed.PPC64LE.Serial

theorem affT_length (lo hi : Vector Byte 16) : (affT lo hi).length = 8 := by simp [affT]

theorem row_affT (lo hi : Vector Byte 16) {c : Nat} (hc : c < 256) :
    Proof.Aes.row (affT lo hi) c = aff lo hi (BitVec.ofNat 8 c) := by
  refine Proof.Aes.row_ext fun j hj => ?_
  simp only [affT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, testBit_tableOf, hc, decide_true, Bool.true_and]

/-! ## The checks, on the tables written out -/

theorem check0 : ∀ c < 256, (aff out0Lo out0Hi (Proof.Aes.row midT c)).toNat =
    (Proof.Aes.row (Proof.Seed.tableT false) c).toNat := by
  lit_decide
theorem check1 : ∀ c < 256, (aff out1Lo out1Hi (Proof.Aes.row midT c)).toNat =
    (Proof.Aes.row (Proof.Seed.tableT true) c).toNat := by
  lit_decide

/-! ## The S-boxes -/

theorem mid_eq (b : Byte) : Proof.Aes.row midT b.toNat = Spec.Aes.sbox (aff inLo inHi b) := by
  rw [midT, Proof.Aes.row_sboxT (affT_length _ _) b.isLt, row_affT _ _ b.isLt, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem s0_affine (b : Byte) :
    aff out0Lo out0Hi (Spec.Aes.sbox (aff inLo inHi b)) = Spec.Seed.s0.getD b.toNat 0 := by
  have e := check0 b.toNat b.isLt
  rw [mid_eq, Proof.Seed.row_tableT _ b.isLt] at e
  exact BitVec.eq_of_toNat_eq e

theorem s1_affine (b : Byte) :
    aff out1Lo out1Hi (Spec.Aes.sbox (aff inLo inHi b)) = Spec.Seed.s1.getD b.toNat 0 := by
  have e := check1 b.toNat b.isLt
  rw [mid_eq, Proof.Seed.row_tableT _ b.isLt] at e
  exact BitVec.eq_of_toNat_eq e

end VG.Proof.Seed.PPC64LE.Serial
