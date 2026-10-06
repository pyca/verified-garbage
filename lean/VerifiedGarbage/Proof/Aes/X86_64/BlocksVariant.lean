import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks

/-!
# Implementations of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86-64

A `BlocksImpl` is what a function that encrypts and decrypts whole blocks
with AES needs of them, so that its proof holds for every implementation:
each is a variant of the interface `AesBlocks` on x86-64
(`Variants/AesBlocks/X86_64/`), and each caller (in
`Generic/AesBlocks/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both functions are proven against the same contract,
`Proof.Aes.blocksX86_64` (with `Spec.Aes.cipher` and `Spec.Aes.invCipher`),
and make no calls. They come with the implementation of `vg_aes_expand_key`
that goes with them (with the same suffix and CPU features), for the callers
that also expand the key, proven against `Proof.Aes.expandKeyX86_64`.
-/

namespace VG.Proof.Aes.X86_64

open VG.X86_64

/-- An implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
on x86-64, and of `vg_aes_expand_key`. -/
structure BlocksImpl where
  /-- `vg_aes_encrypt_blocks`: its symbol and code. -/
  enc : Impl.Aes.X86_64.Blocks
  encDepth : enc.code.depth = 0
  encOk : ∀ s, (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub enc.code
  encNosp : NoSp enc.code
  encMxcsr : enc.code.allInstrs (fun i => !loadsMxcsr i) = true
  encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true
  encNoStack : enc.code.x86_64Depth = 0
  /-- `vg_aes_decrypt_blocks`: its symbol and code. -/
  dec : Impl.Aes.X86_64.Blocks
  decDepth : dec.code.depth = 0
  decOk : ∀ s, (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s'
  decCt : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub dec.code
  decNosp : NoSp dec.code
  decMxcsr : dec.code.allInstrs (fun i => !loadsMxcsr i) = true
  decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true
  decNoStack : dec.code.x86_64Depth = 0
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.X86_64.ExpandKey
  expandDepth : expand.code.depth = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86_64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub expand.code
  expandNosp : NoSp expand.code
  expandMxcsr : expand.code.allInstrs (fun i => !loadsMxcsr i) = true
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
  expandNoStack : expand.code.x86_64Depth = 0

namespace BlocksImpl

theorem nosp_of {c : Prog isa}
    (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

/-- The bitsliced implementation, `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks`, in the baseline ISA. -/
def scalar : BlocksImpl where
  enc := .encScalar
  encDepth := by decide +kernel
  encOk := encryptBlocks_correct
  encCt := encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
  encMxcsr := by decide +kernel
  encSpSafe := Code.all_of_allInstrs (by decide +kernel)
  encNoStack := by decide +kernel
  dec := .decScalar
  decDepth := by decide +kernel
  decOk := decryptBlocks_correct
  decCt := decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
  decMxcsr := by decide +kernel
  decSpSafe := Code.all_of_allInstrs (by decide +kernel)
  decNoStack := by decide +kernel
  suffix := ""
  features := []
  expand := .scalar
  expandDepth := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandNosp := Ctr32Impl.expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)
  expandNoStack := by lit_decide

/-- The AES-NI implementation, `vg_aes_encrypt_blocks_aesni` and
`vg_aes_decrypt_blocks_aesni`, with `vg_aes_expand_key_aesni`. -/
def aesni : BlocksImpl where
  enc := .encAesni
  encDepth := by decide +kernel
  encOk := AesNi.encryptBlocks_correct
  encCt := AesNi.encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
  encMxcsr := by decide +kernel
  encSpSafe := Code.all_of_allInstrs (by decide +kernel)
  encNoStack := by decide +kernel
  dec := .decAesni
  decDepth := by decide +kernel
  decOk := AesNi.decryptBlocks_correct
  decCt := AesNi.decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
  decMxcsr := by decide +kernel
  decSpSafe := Code.all_of_allInstrs (by decide +kernel)
  decNoStack := by decide +kernel
  suffix := "_aesni"
  features := ["aes"]
  expand := .aesni
  expandDepth := by lit_decide
  expandOk := Ctr32Impl.aesni_expandKey_ok
  expandCt := Ctr32Impl.aesni_expandKey_ct
  expandNosp := Ctr32Impl.aesni_expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)
  expandNoStack := by lit_decide

end BlocksImpl

end VG.Proof.Aes.X86_64
