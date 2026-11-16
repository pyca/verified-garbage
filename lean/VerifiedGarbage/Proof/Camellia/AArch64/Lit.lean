module

public import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Camellia.SboxTable
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
meta import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
meta import VerifiedGarbage.Proof.Camellia.SboxTable
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Camellia on AArch64: the code as literals

The code of the key expansion, of ECB in both directions, of the preparation
of the subkeys and of a batch under them, of the serial core's two
functions, of CTR and of CBC in both
directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again (seconds for the key expansion's).
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

/-- A number below 256 is the sum of its bits. -/
theorem byte_bits : ∀ n < 256, (List.range 8).foldl (fun b k => b + (n.testBit k).toNat * 2 ^ k) 0 = n := by
  decide +kernel

/-- `SBOX1`'s entry `i` as a number, from the truth tables of its bits
(`Proof/Camellia/SboxTable.lean`). -/
theorem sbox1Table_toNat (i : Nat) : (Spec.Camellia.sbox1Table.getD i 0).toNat =
    if i < 256 then
      (List.range 8).foldl (fun b k => b + ((Proof.Camellia.sbox1T k).testBit i).toNat * 2 ^ k) 0
    else 0 := by
  split
  · rename_i hi
    have hs : Spec.Camellia.sbox1 (BitVec.ofNat 8 i) = Spec.Camellia.sbox1Table.getD i 0 := by
      rw [Spec.Camellia.sbox1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [Proof.Camellia.testBit_sbox1T hi, hs, ← BitVec.testBit_toNat]
    exact (byte_bits _ (Spec.Camellia.sbox1Table.getD i 0).isLt).symm
  · rename_i hi
    rw [Vector.getD, Array.getD, dite_eq_right (by simpa using hi)]
    rfl

/-- The code that loads `SBOX1` by immediates, its bytes read from the truth
tables of their bits. -/
private def sbox1Load : List VG.AArch64.Instr :=
  Impl.Tbl.AArch64.loadTable fun i => BitVec.ofNat 8 (if i < 256 then
    (List.range 8).foldl (fun b k => b + ((Proof.Camellia.sbox1T k).testBit i).toNat * 2 ^ k) 0 else 0)

materialize_value sbox1Load

/-- The literal of the code that loads `SBOX1` as the key expansion has it,
looking each byte up in the specification's vector, which flattens its rows
and walks to the entry at every lookup (private: only this module's
literals contain that code outside a literal). -/
private noncomputable abbrev sbox1Code.lit : List VG.AArch64.Instr := sbox1Load.lit

private theorem sbox1Code.lit_eq :
    Impl.Tbl.AArch64.loadTable (fun k => Spec.Camellia.sbox1Table.getD k 0) = sbox1Code.lit :=
  (congrArg Impl.Tbl.AArch64.loadTable (funext fun i => by
    rw [← sbox1Table_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq])).trans sbox1Load.lit_eq

materialize_flat_code expandKeyCode := Impl.Camellia.AArch64.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.AArch64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.AArch64.ecb .decrypt
materialize_flat_code prepareKeysCode := Impl.Camellia.AArch64.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Camellia.AArch64.cryptPrepared
materialize_flat_code ctrCode := Impl.Camellia.AArch64.ctr
/-- `tableWord`, `SBOX1`'s entries read from the truth tables of their bits,
which the kernel has evaluated in one pass over the specification's table
(`sbox1T`): the table's literal below reads its 256 bytes through this
(`unfoldToLits` rewrites `tableWord` to it, as to a table of
`materialize_table`) rather than look each up in the specification's
vector, which flattens its rows and walks to the entry at every lookup. -/
noncomputable abbrev _root_.VG.Impl.Camellia.AArch64.Serial.tableWord.lit (h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 <| (List.range 8).foldl (fun a j => a +
    (if 8 * h + j < 256 then
      (List.range 8).foldl (fun b k => b + ((Proof.Camellia.sbox1T.lit k).testBit (8 * h + j)).toNat * 2 ^ k) 0
    else 0) * 2 ^ (8 * j)) 0

theorem _root_.VG.Impl.Camellia.AArch64.Serial.tableWord.lit_eq :
    Impl.Camellia.AArch64.Serial.tableWord = Impl.Camellia.AArch64.Serial.tableWord.lit := by
  funext h
  rw [Impl.Camellia.AArch64.Serial.tableWord, Impl.Camellia.AArch64.Serial.tableWord.lit,
    ← Proof.Camellia.sbox1T.lit_eq]
  simp only [sbox1Table_toNat]

materialize_value serialTable := Impl.Camellia.AArch64.Serial.table
materialize_code serialPrepareCode := Impl.Camellia.AArch64.Serial.prepareEncrypt
materialize_code serialCryptCode := Impl.Camellia.AArch64.Serial.encryptPrepared
materialize_code cbcEncryptChainedCode := Impl.Camellia.AArch64.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Camellia.AArch64.cbcDecryptChained

end VG.Proof.Camellia.AArch64
