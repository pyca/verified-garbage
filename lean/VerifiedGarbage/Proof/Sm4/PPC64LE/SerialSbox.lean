module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Serial
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Serial
public import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Sm4.SboxTable
meta import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4's S-box through the AES S-box, on all 256 inputs

`sbox_affine`: the single-block core's S-box (`Impl/Sm4/PPC64LE/Serial.lean`),
the affine map of the tables `inLo` and `inHi`, the AES S-box, and the
affine map of `outLo` and `outHi` (`aff`), is SM4's on every byte. The
kernel evaluates the AES S-box of the 256 images of `A_in` at once, on
truth tables (`Proof.Aes.sboxT`, `midT`, written out once by
`materialize_value`), then checks each input against SM4's S-box.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Serial

open VG VG.Bitslice
open VG.Impl.Sm4.PPC64LE.Serial

/-- An affine map on bytes, by the tables of its low and high nibbles. -/
def aff (lo hi : Vector Byte 16) (b : Byte) : Byte := lo.getD (b &&& 0x0f).toNat 0 ^^^ hi.getD (b >>> 4).toNat 0

/-- `A_in` on the input `c`. -/
def ainN (c : Nat) : Byte := aff inLo inHi (BitVec.ofNat 8 c)

/-- The truth tables of `A_in`. -/
def ainT : List Nat := (List.range 8).map fun j => tableOf (fun c => (ainN c).getLsbD j) 256

/-- The AES S-box of `A_in`, on all inputs. -/
def midT : List Nat := Proof.Aes.sboxT ainT

end VG.Proof.Sm4.PPC64LE.Serial

namespace VG

materialize_value Proof.Sm4.PPC64LE.Serial.midT

end VG

namespace VG.Proof.Sm4.PPC64LE.Serial

open VG VG.Bitslice
open VG.Impl.Sm4.PPC64LE.Serial

theorem ainT_length : ainT.length = 8 := by simp [ainT]

theorem row_ainT {c : Nat} (hc : c < 256) : Proof.Aes.row ainT c = ainN c := by
  refine Proof.Aes.row_ext fun j hj => ?_
  simp only [ainT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, testBit_tableOf, hc, decide_true, Bool.true_and]

/-- The check, on the tables written out. -/
theorem check : ∀ c < 256, (aff outLo outHi (Proof.Aes.row midT c)).toNat = Proof.Sm4.sboxN c := by
  lit_decide

theorem sbox_affine (b : Byte) :
    aff outLo outHi (Spec.Aes.sbox (aff inLo inHi b)) = Spec.Sm4.sbox.getD b.toNat 0 := by
  have hb := b.isLt
  have e := check b.toNat hb
  rw [midT, Proof.Aes.row_sboxT ainT_length hb, row_ainT hb, ainN, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Proof.Sm4.sboxN_eq hb, BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact BitVec.eq_of_toNat_eq e

end VG.Proof.Sm4.PPC64LE.Serial
