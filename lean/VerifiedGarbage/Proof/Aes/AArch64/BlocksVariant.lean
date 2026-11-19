module

public import VerifiedGarbage.Proof.Aes.AArch64.Variant
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.OneBlock
public import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Implementations of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on AArch64

A `BlocksImpl` is what a function that encrypts and decrypts whole blocks
with AES needs of them, so that its proof holds for every implementation:
each is a variant of the interface `AesBlocks` on AArch64
(`Variants/AesBlocks/AArch64/`), and each caller (in
`Generic/AesBlocks/AArch64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both functions are proven against the same contract,
`Proof.Aes.blocksAArch64` (with `Spec.Aes.cipher` and `Spec.Aes.invCipher`),
and have no frames. They come with the implementation of `vg_aes_expand_key`
that goes with them (with the same suffix and CPU features), for the callers
that also expand the key, proven against `Proof.Aes.expandKeyAArch64`.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64

open VG.AArch64

/-- An implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
on AArch64, and of `vg_aes_expand_key`. -/
structure BlocksImpl where
  /-- `vg_aes_encrypt_blocks`: its symbol and code. -/
  enc : Impl.Aes.AArch64.Blocks
  encNoFrames : enc.code.noFrames = true
  encOk : ∀ s, (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub enc.code
  encKeepsV : enc.code.allInstrs keepsV = true
  /-- `vg_aes_decrypt_blocks`: its symbol and code. -/
  dec : Impl.Aes.AArch64.Blocks
  decNoFrames : dec.code.noFrames = true
  decOk : ∀ s, (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s'
  decCt : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pub dec.code
  decKeepsV : dec.code.allInstrs keepsV = true
  /-- The bytes of `scratch` both functions need: none, or
  `blocksAArch64`'s 2048. A caller allocates only these
  (`blocksAArch64With`), so that it has less of its stack to zero on
  return. -/
  scratch : Nat
  scratch_ok : scratch = 0 ∨ scratch = 2048
  encOkW : ∀ s, (Proof.Aes.blocksAArch64With scratch Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64With scratch Spec.Aes.cipher).post s s'
  encCtW : ConstantTime isa (Proof.Aes.blocksAArch64With scratch Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64With scratch Spec.Aes.cipher).pub enc.code
  decOkW : ∀ s, (Proof.Aes.blocksAArch64With scratch Spec.Aes.invCipher).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64With scratch Spec.Aes.invCipher).post s s'
  decCtW : ConstantTime isa (Proof.Aes.blocksAArch64With scratch Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64With scratch Spec.Aes.invCipher).pub dec.code
  /-- Whether both functions write nothing in `scratch` (`encFree`,
  `decFree`), so that a caller that leaves nothing written there need not
  wipe it. -/
  free : Bool
  encFree : free = true → ∀ s t s', (Proof.Aes.encryptBlocksRoundsContract AArch64.abi).pre s →
    Exec isa enc.code s t s' →
      Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s'
  decFree : free = true → ∀ s t s', (Proof.Aes.decryptBlocksRoundsContract AArch64.abi).pre s →
    Exec isa dec.code s t s' →
      Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s'
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The registers `enc.code`, `dec.code` and `expand.code` write: a caller's tail clears
  them with its own (`ScrubAll.clearUnion`), and its `ScrubAll.scrubSide`
  holds them to the code. -/
  encClear : Impl.Residue.AArch64.Clear
  decClear : Impl.Residue.AArch64.Clear
  expandClear : Impl.Residue.AArch64.Clear
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.AArch64.ExpandKey
  expandNoFrames : expand.code.noFrames = true
  expandOk : ∀ s, Proof.Aes.expandKeyAArch64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyAArch64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyAArch64.pre Proof.Aes.expandKeyAArch64.pub expand.code
  expandKeepsV : expand.code.allInstrs AArch64.keepsV = true
  /-- The vector registers `vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`,
  whose code is `enc`'s and `dec`'s where they write nothing in `scratch`,
  clear before they return (`Impl.Residue.AArch64.withClears`), and, where the
  residue analysis checks it, that they then return without secret residue.
  `enc` and `dec` themselves, which callers call by name for as little as a
  block, keep what they leave. -/
  ecbClear : List VReg := []
  ecbClearOk : (Impl.Residue.AArch64.clears [] ecbClear none).all Clears.clearOk = true := by decide
  encRes : Option (PLift (∀ k, NoResidue (Impl.Residue.AArch64.withClears [] ecbClear none enc.code) k 0)) :=
    none
  decRes : Option (PLift (∀ k, NoResidue (Impl.Residue.AArch64.withClears [] ecbClear none dec.code) k 0)) :=
    none

namespace BlocksImpl

/-- The implementation in the baseline ISA, `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks`: each block by vector permutations
(`OneBlock.lean`). -/
def scalar : BlocksImpl where
  enc := .encScalar
  encNoFrames := by lit_decide
  encOk := OneBlock.encryptBlocksN_correct
  encCt := OneBlock.encryptBlocksN_ct
  encKeepsV := by lit_decide
  dec := .decScalar
  decNoFrames := by lit_decide
  decOk := OneBlock.decryptBlocksN_correct
  decCt := OneBlock.decryptBlocksN_ct
  decKeepsV := by lit_decide
  scratch := 2048
  scratch_ok := .inr rfl
  encOkW := by rw [Proof.Aes.blocksAArch64With_2048]; exact OneBlock.encryptBlocksN_correct
  encCtW := by rw [Proof.Aes.blocksAArch64With_2048]; exact OneBlock.encryptBlocksN_ct
  decOkW := by rw [Proof.Aes.blocksAArch64With_2048]; exact OneBlock.decryptBlocksN_correct
  decCtW := by rw [Proof.Aes.blocksAArch64With_2048]; exact OneBlock.decryptBlocksN_ct
  free := false
  encFree := nofun
  decFree := nofun
  suffix := ""
  features := []
  encClear := ⟨[.x1, .x2, .x3, .x6, .x9, .x10],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30, .v31],
    []⟩
  decClear := ⟨[.x1, .x2, .x3, .x6, .x9, .x10],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30],
    []⟩
  expandClear := ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30, .v31],
    []⟩
  expand := .scalar
  expandNoFrames := Ctr32Impl.scalar.expandNoFrames
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandKeepsV := Ctr32Impl.scalar.expandKeepsV

/-- The implementation with the Cryptographic Extension,
`vg_aes_encrypt_blocks_aes` and `vg_aes_decrypt_blocks_aes`, with
`vg_aes_expand_key_aes`. -/
def aese : BlocksImpl where
  enc := .encAese
  encNoFrames := by lit_decide
  encOk := Aese.encryptBlocks_correct
  encCt := Aese.encryptBlocks_ct
  encKeepsV := by lit_decide
  dec := .decAese
  decNoFrames := by lit_decide
  decOk := Aese.decryptBlocks_correct
  decCt := Aese.decryptBlocks_ct
  decKeepsV := by lit_decide
  scratch := 0
  scratch_ok := .inl rfl
  encOkW := Aese.encryptBlocks_correctW 0
  encCtW := Aese.encryptBlocks_ctW 0
  decOkW := Aese.decryptBlocks_correctW 0
  decCtW := Aese.decryptBlocks_ctW 0
  free := true
  encFree := fun _ => Aese.encryptBlocks_written
  decFree := fun _ => Aese.decryptBlocks_written
  suffix := "_aes"
  features := ["aes"]
  encClear := ⟨[.x2, .x3, .x6, .x7, .x9, .x13],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30],
    []⟩
  decClear := ⟨[.x2, .x3, .x6, .x7, .x9, .x13],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30],
    []⟩
  expandClear := ⟨[.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13],
    [.v0, .v1],
    []⟩
  expand := .aese
  expandNoFrames := Ctr32Impl.aese.expandNoFrames
  expandOk := Ctr32Impl.aese.expandOk
  expandCt := Ctr32Impl.aese.expandCt
  expandKeepsV := Ctr32Impl.aese.expandKeepsV
  ecbClear := Aese.blocksLeft
  encRes := some ⟨Aese.encryptBlocks_noResidue⟩
  decRes := some ⟨Aese.decryptBlocks_noResidue⟩

end BlocksImpl

end VG.Proof.Aes.AArch64
