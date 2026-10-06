import VerifiedGarbage.Proof.Aes.AArch64.Variant
import VerifiedGarbage.Proof.Aes.AArch64.Blocks
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks

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
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.AArch64.ExpandKey
  expandNoFrames : expand.code.noFrames = true
  expandOk : ∀ s, Proof.Aes.expandKeyAArch64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyAArch64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyAArch64.pre Proof.Aes.expandKeyAArch64.pub expand.code
  expandKeepsV : expand.code.allInstrs AArch64.keepsV = true

namespace BlocksImpl

/-- The bitsliced implementation, `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks`, in the baseline ISA. -/
def scalar : BlocksImpl where
  enc := .encScalar
  encNoFrames := by decide +kernel
  encOk := encryptBlocks_correct
  encCt := encryptBlocks_ct
  encKeepsV := by decide +kernel
  dec := .decScalar
  decNoFrames := by decide +kernel
  decOk := decryptBlocks_correct
  decCt := decryptBlocks_ct
  decKeepsV := by decide +kernel
  suffix := ""
  features := []
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
  encNoFrames := by decide +kernel
  encOk := Aese.encryptBlocks_correct
  encCt := Aese.encryptBlocks_ct
  encKeepsV := by decide +kernel
  dec := .decAese
  decNoFrames := by decide +kernel
  decOk := Aese.decryptBlocks_correct
  decCt := Aese.decryptBlocks_ct
  decKeepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  expand := .aese
  expandNoFrames := Ctr32Impl.aese.expandNoFrames
  expandOk := Ctr32Impl.aese.expandOk
  expandCt := Ctr32Impl.aese.expandCt
  expandKeepsV := Ctr32Impl.aese.expandKeepsV

end BlocksImpl

end VG.Proof.Aes.AArch64
