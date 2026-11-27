module

public import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Aes.Vector
meta import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Aes.AArch64.Blocks
meta import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES on AArch64: the entry points, as literals

The code of the key expansion, CTR32 and the block functions, in their
bitsliced and AESE forms, built by functions, as literals
(`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`, the registration file's `spSafe`) read the literal instead of
building the code again.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64

open VG.Bitslice VG.VectorCrypto

/-! ## The S-box of the key expansion's static

The static the key expansion loads holds the S-box (`OneBlock.tabWords`),
which the kernel would evaluate byte by byte, an inverse in GF(2⁸) each, and
each byte for both words of its vector. The specification's S-box is
evaluated on truth tables instead, on the 256 bytes at once
(`Proof/Aes/SboxSpec.lean`), and the model's S-box is a table read from them
(`sbox.lit_eq`), which the literal of the static reads. -/

/-- The truth tables of the bits of a byte, on the 256 bytes. -/
private def inTabs : List Nat := (List.range 8).map fun k => tableOf (fun c => c.testBit k) 256

/-- The specification's S-box on the 256 bytes, as truth tables. -/
private def sboxTabs : List Nat := sboxT inTabs

/-- The S-box of byte `c`, read from the truth tables. -/
private def sboxN (c : Nat) : Nat := (row sboxTabs c).toNat

private theorem row_inTabs {c : Nat} (hc : c < 256) : row inTabs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTabs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

private theorem aesSbox_eq_sboxN : aesSbox = fun b => BitVec.ofNat 8 (sboxN b.toNat) := by
  funext b
  rw [sboxN, sboxTabs, row_sboxT (by simp [inTabs]) b.isLt, row_inTabs b.isLt, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq, Vector.sbox_eq]

materialize_value sboxTabs
materialize_table sboxN 256

/-- The model's S-box, read from the table: the literal of `aesSbox` in this
module (it is private, so that the checks of other modules do not look for
the S-box in their code). -/
private noncomputable abbrev sbox.lit : BitVec 8 → BitVec 8 := fun b => BitVec.ofNat 8 (sboxN.lit b.toNat)

private theorem sbox.lit_eq : aesSbox = sbox.lit :=
  aesSbox_eq_sboxN.trans
    (congrArg (fun f : Nat → Nat => fun b : BitVec 8 => BitVec.ofNat 8 (f b.toNat)) sboxN.lit_eq)

end VG.Proof.Aes.AArch64

namespace VG.Impl.Aes.AArch64
materialize_value OneBlock.tabWords
materialize_code expandKey
materialize_code ctr32N
materialize_code ctr32ToN
materialize_code encryptBlocksN
materialize_code decryptBlocksN
end VG.Impl.Aes.AArch64

namespace VG.Impl.Aes.AArch64.Aese
materialize_code expandKey
materialize_code ctr32
materialize_code ctr32To
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.AArch64.Aese
