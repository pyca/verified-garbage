import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Aes.X86.BlocksCT
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain

/-!
# Implementations of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86

A `BlocksImpl` is what a function that encrypts and decrypts whole blocks
with AES needs of them, so that its proof holds for every implementation:
each is a variant of the interface `AesBlocks` on x86
(`Variants/AesBlocks/X86/`), and each caller (in `Generic/AesBlocks/X86/`)
is emitted once for each of them (see `TCB/Emit.lean`). Both functions are
proven against the same contract, `Proof.Aes.blocksX86` (with
`Spec.Aes.cipher` and `Spec.Aes.invCipher`), and make no calls. They come
with the implementation of `vg_aes_expand_key` that goes with them (with
the same suffix and CPU features), for the callers that also expand the
key, proven against `Proof.Aes.expandKeyX86`.
-/

namespace VG.Impl.Aes.X86
materialize_code encryptBlocks
materialize_code decryptBlocks
namespace AesNi
materialize_code encryptBlocks
materialize_code decryptBlocks
end AesNi
end VG.Impl.Aes.X86

namespace VG.Proof.Aes.X86

open VG.X86

/-- An implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
on x86, and of `vg_aes_expand_key`. -/
structure BlocksImpl where
  /-- `vg_aes_encrypt_blocks`: its symbol and code. -/
  enc : Impl.Aes.X86.Blocks
  encStack : stackUse enc.code = 0
  encOk : ∀ s, (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre (Proof.Aes.blocksX86 Spec.Aes.cipher).pub
    enc.code
  encNosp : NoSp enc.code
  encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true
  /-- `vg_aes_decrypt_blocks`: its symbol and code. -/
  dec : Impl.Aes.X86.Blocks
  decStack : stackUse dec.code = 0
  decOk : ∀ s, (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s'
  decCt : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub dec.code
  decNosp : NoSp dec.code
  decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.X86.ExpandKey
  expandStack : stackUse expand.code = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86.pre Proof.Aes.expandKeyX86.pub expand.code
  expandNosp : NoSp expand.code
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true

namespace BlocksImpl

/-- The bitsliced implementation, in the baseline ISA. -/
def scalar : BlocksImpl where
  enc := .encScalar
  encStack := by lit_decide
  encOk := encryptBlocks_correct
  encCt := encryptBlocks_ct
  encNosp := NoSp.of_all (by lit_decide)
  encSpSafe := Code.all_of_allInstrs (by lit_decide)
  dec := .decScalar
  decStack := by lit_decide
  decOk := decryptBlocks_correct
  decCt := decryptBlocks_ct
  decNosp := NoSp.of_all (by lit_decide)
  decSpSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  expand := Ctr32Impl.scalar.expand
  expandStack := Ctr32Impl.scalar.expandStack
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandNosp := Ctr32Impl.scalar.expandNosp
  expandSpSafe := Ctr32Impl.scalar.expandSpSafe

/-- AES-NI. -/
def aesni : BlocksImpl where
  enc := .encAesni
  encStack := by lit_decide
  encOk := AesNi.encryptBlocks_correct
  encCt := AesNi.encryptBlocks_ct
  encNosp := NoSp.of_all (by lit_decide)
  encSpSafe := Code.all_of_allInstrs (by lit_decide)
  dec := .decAesni
  decStack := by lit_decide
  decOk := AesNi.decryptBlocks_correct
  decCt := AesNi.decryptBlocks_ct
  decNosp := NoSp.of_all (by lit_decide)
  decSpSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_aesni"
  features := ["aes"]
  expand := Ctr32Impl.aesni.expand
  expandStack := Ctr32Impl.aesni.expandStack
  expandOk := Ctr32Impl.aesni.expandOk
  expandCt := Ctr32Impl.aesni.expandCt
  expandNosp := Ctr32Impl.aesni.expandNosp
  expandSpSafe := Ctr32Impl.aesni.expandSpSafe

end BlocksImpl

end VG.Proof.Aes.X86
