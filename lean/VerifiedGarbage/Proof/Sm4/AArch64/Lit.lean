module

public import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Key
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
public import VerifiedGarbage.Proof.Sm4.SboxTable
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
meta import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Key
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.SboxTable
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM4 on AArch64: the code as literals

The code of the key expansion, of ECB in both directions, of the preparation
of the round keys and of a batch under them, of CTR and of CBC in both
directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Serial

/-- A word of the serial code's table of the S-box, its bytes read in the
S-box's packed table (`Proof.Sm4.sboxN.lit`): the literal of the code that
stores the table (`serialTable` below) reads the words here, where the kernel
would look up each byte in the specification's vector, which it builds by
256 `push`es and walks to the byte. -/
noncomputable def tableWord.lit (h : Nat) : BitVec 64 := BitVec.ofNat 64 <| (List.range 8).foldl
  (fun a j => a + Proof.Sm4.sboxN.lit (8 * h + j) * 2 ^ (8 * j)) 0

theorem tableWord.lit_eq : tableWord = tableWord.lit := by
  funext h
  simp only [tableWord, tableWord.lit, ← Proof.Sm4.sboxN.lit_eq, Proof.Sm4.sboxN_getD]

end VG.Impl.Sm4.AArch64.Serial

namespace VG.Proof.Sm4.AArch64

/-! The key expansion loads the S-box by immediates (`Impl.Tbl.AArch64.loadTable`),
a lookup in the specification's vector for each of its 256 bytes. The code
that loads it is evaluated once here, its bytes read from the packed table
(`Proof.Sm4.sboxN.lit`), and is the literal of the code the key expansion
contains (`sboxLoad.lit_eq`), as for SEED (`Proof/Seed/AArch64/ModesLit.lean`). -/

/-- The code that loads the S-box, its bytes from the packed table. -/
private def sboxPacked : List VG.AArch64.Instr :=
  Impl.Tbl.AArch64.loadTable (fun k => BitVec.ofNat 8 (Proof.Sm4.sboxN k))

materialize_value sboxPacked

/-- The literal of the code that loads the S-box (private: only this module's
literals contain that code outside a literal). -/
private noncomputable abbrev sboxLoad.lit : List VG.AArch64.Instr := sboxPacked.lit

private theorem sboxLoad.lit_eq :
    Impl.Tbl.AArch64.loadTable (fun k => Spec.Sm4.sbox.getD k 0) = sboxLoad.lit := by
  have e : (fun k => Spec.Sm4.sbox.getD k 0) = fun k => BitVec.ofNat 8 (Proof.Sm4.sboxN k) := by
    funext k
    rw [Proof.Sm4.sboxN_getD, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e]
  exact sboxPacked.lit_eq

materialize_flat_code serialExpandKeyCode := Impl.Sm4.AArch64.Serial.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.AArch64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.AArch64.ecb .decrypt
materialize_flat_code ecbAnyCode := Impl.Sm4.AArch64.ecbAny
materialize_flat_code prepareKeysCode := Impl.Sm4.AArch64.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Sm4.AArch64.cryptPrepared
materialize_flat_code ctrCode := Impl.Sm4.AArch64.ctr
materialize_value serialTable := Impl.Sm4.AArch64.Serial.preparedTable
materialize_code cbcEncryptChainedCode := Impl.Sm4.AArch64.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Sm4.AArch64.cbcDecryptChained

end VG.Proof.Sm4.AArch64
