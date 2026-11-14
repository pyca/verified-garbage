module

public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Blocks
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Spec.AesEcb.Contract
public import VerifiedGarbage.Impl.AesCfb8.X86_64
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Impl.AesCfb.X86_64
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Impl.AesOfb.X86_64
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Impl.AesOcb.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Implementations of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86-64

A `BlocksImpl` is what a function that encrypts and decrypts whole blocks
with AES needs of them, so that its proof holds for every implementation:
each is a variant of the interface `AesBlocks` on x86-64
(`Variants/AesBlocks/X86_64/`), and each caller (in
`Generic/AesBlocks/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both functions are proven against the same contract,
`Proof.Aes.blocksX86_64` (with `Spec.Aes.cipher` and `Spec.Aes.invCipher`),
and make no calls. Each states how much of `scratch` its functions may write
(`encWritten`, `decWritten`), so that its callers zero only that. They come with the implementation of `vg_aes_expand_key`
that goes with them (with the same suffix and CPU features), for the callers
that also expand the key, proven against `Proof.Aes.expandKeyX86_64`.
An implementation also gives the residue analyses of the functions over it
that the analysis handles (`cfb8EncRes`, `cfb8DecRes`, `ecbEncRes`): those
instances then return without secret residue (`X86_64.RScrub.withScrub`).
One whose encryption and key expansion never touch their scratch buffers
gives their contracts without them (`free`), and the analysis of
`vg_aes_ocb_init` over it with no working space for them (`ocbInitRes`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64

open VG.X86_64

/-- What an implementation whose encryption and key expansion never touch
their scratch buffers gives: their contracts without them
(`Proof.Aes.blocksX86_64F`, `AesNi.Key.expandKey3X86_64`), so that a caller
of those alone needs no working space for them. -/
structure BlocksFree (enc : Impl.Aes.X86_64.Blocks) (expand : Impl.Aes.X86_64.ExpandKey) : Type where
  encOk : ∀ s, (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64F Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pub enc.code
  expandOk : ∀ s, AesNi.Key.expandKey3X86_64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ AesNi.Key.expandKey3X86_64.post s s'
  expandCt : ConstantTime isa AesNi.Key.expandKey3X86_64.pre AesNi.Key.expandKey3X86_64.pub expand.code

/-- `vg_aes_ocb_init`'s code over `enc`, `dec` and `expand` when encryption
and the key expansion need no working space (`BlocksFree`): a frame of only
the 24 bytes `init` writes itself. -/
def ocbInitCodeF (enc dec : Impl.Aes.X86_64.Blocks) (expand : Impl.Aes.X86_64.ExpandKey) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨enc, dec, expand⟩)

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
  /-- `enc` writes no byte of `scratch` at offset `encWritten` or beyond:
  its callers need to zero only the first `encWritten` bytes. -/
  encWritten : Nat
  encWrittenLe : encWritten ≤ 2048
  encWrittenOk : ∀ s t s', (Proof.Aes.encryptBlocksRoundsContract X86_64.abi).pre s →
    Exec isa enc.code s t s' →
      Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", encWritten)] s s'
  /-- `dec` writes no byte of `scratch` at offset `decWritten` or beyond. -/
  decWritten : Nat
  decWrittenLe : decWritten ≤ 2048
  decWrittenOk : ∀ s t s', (Proof.Aes.decryptBlocksRoundsContract X86_64.abi).pre s →
    Exec isa dec.code s t s' →
      Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", decWritten)] s s'
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
  /-- The residue analysis of `vg_aes_cfb8_encrypt` over it, if the analysis
  handles it. -/
  cfb8EncRes : Option (RScrub.Analysed Spec.Cfb8.aesEncryptApi.sig 8 []
    (Impl.AesCfb8.X86_64.encrypt enc)) := none
  /-- The residue analysis of `vg_aes_cfb8_decrypt` over it, if the analysis
  handles it. -/
  cfb8DecRes : Option (RScrub.Analysed Spec.Cfb8.aesDecryptApi.sig 8 []
    (Impl.AesCfb8.X86_64.decrypt enc)) := none
  /-- The residue analysis of `vg_aes_cfb128_encrypt` over it, if the
  analysis handles it. -/
  cfbEncRes : Option (RScrub.Analysed Spec.Cfb.aesEncryptApi.sig 8 []
    (Impl.AesCfb.X86_64.encrypt enc)) := none
  /-- The residue analysis of `vg_aes_cfb128_decrypt` over it, if the
  analysis handles it. -/
  cfbDecRes : Option (RScrub.Analysed Spec.Cfb.aesDecryptApi.sig 8 []
    (Impl.AesCfb.X86_64.decrypt enc)) := none
  /-- The residue analysis of `vg_aes_ofb` over it, if the analysis handles
  it. -/
  ofbRes : Option (RScrub.Analysed Spec.Ofb.aesApi.sig 8 [] (Impl.AesOfb.X86_64.crypt enc)) := none
  /-- The residue analysis of `vg_aes_ecb_encrypt` as its `enc` alone, if
  the analysis handles it. -/
  ecbEncRes : Option (RScrub.Analysed Spec.AesEcb.encryptApi.sig 0 [] enc.code) := none
  /-- The contracts of encryption and the key expansion without a scratch
  buffer, if they never touch one. -/
  free : Option (BlocksFree enc expand) := none
  /-- The residue analysis of `vg_aes_ocb_init` over it, without working
  space for it (`free`), if the analysis handles it. -/
  ocbInitRes : Option (RScrub.Analysed Spec.Ocb.initApi.sig 40 [] (ocbInitCodeF enc dec expand)) := none

namespace BlocksImpl

theorem nosp_of {c : Prog isa}
    (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

/-- Any run writes none of `scratch` from its end on. -/
theorem written_all (s s' : State) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 2048)] s s' := by
  simp [Sig.writtenWithin, X86_64.abi, X86_64.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits, Elem.size]
  intro i h1 h2
  omega

/-- The bitsliced implementation, `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks`, in the baseline ISA. -/
def scalar : BlocksImpl where
  enc := .encScalar
  encDepth := by lit_decide
  encOk := encryptBlocks_correct
  encCt := encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  encMxcsr := by lit_decide
  encSpSafe := Code.all_of_allInstrs (by lit_decide)
  encNoStack := by lit_decide
  dec := .decScalar
  decDepth := by lit_decide
  decOk := decryptBlocks_correct
  decCt := decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  decMxcsr := by lit_decide
  decSpSafe := Code.all_of_allInstrs (by lit_decide)
  decNoStack := by lit_decide
  encWritten := 2048
  encWrittenLe := Nat.le_refl _
  encWrittenOk := fun s _ s' _ _ => written_all s s'
  decWritten := 2048
  decWrittenLe := Nat.le_refl _
  decWrittenOk := fun s _ s' _ _ => written_all s s'
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
  encDepth := by lit_decide
  encOk := AesNi.encryptBlocks_correct
  encCt := AesNi.encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  encMxcsr := by lit_decide
  encSpSafe := Code.all_of_allInstrs (by lit_decide)
  encNoStack := by lit_decide
  dec := .decAesni
  decDepth := by lit_decide
  decOk := AesNi.decryptBlocks_correct
  decCt := AesNi.decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  decMxcsr := by lit_decide
  decSpSafe := Code.all_of_allInstrs (by lit_decide)
  decNoStack := by lit_decide
  encWritten := 0
  encWrittenLe := Nat.zero_le _
  encWrittenOk := AesNi.encryptBlocks_written
  decWritten := 224
  decWrittenLe := by decide
  decWrittenOk := AesNi.decryptBlocks_written
  free := some ⟨AesNi.encryptBlocksF_correct, AesNi.encryptBlocks_ctP, AesNi.Key.expandKey3_correct,
    AesNi.Key.expandKey3_ct⟩
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

/-- The VAES implementation, `vg_aes_encrypt_blocks_vaes` and
`vg_aes_decrypt_blocks_vaes` (sixteen blocks at a time, then AES-NI's
loops), with `vg_aes_expand_key_aesni`. -/
def vaes : BlocksImpl where
  enc := .encVaes
  encDepth := by lit_decide
  encOk := VaesBlocks.encryptBlocks_correct
  encCt := VaesBlocks.encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  encMxcsr := by lit_decide
  encSpSafe := Code.all_of_allInstrs (by lit_decide)
  encNoStack := by lit_decide
  dec := .decVaes
  decDepth := by lit_decide
  decOk := VaesBlocks.decryptBlocks_correct
  decCt := VaesBlocks.decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  decMxcsr := by lit_decide
  decSpSafe := Code.all_of_allInstrs (by lit_decide)
  decNoStack := by lit_decide
  encWritten := 0
  encWrittenLe := Nat.zero_le _
  encWrittenOk := VaesBlocks.encryptBlocks_written
  decWritten := 224
  decWrittenLe := by decide
  decWrittenOk := VaesBlocks.decryptBlocks_written
  free := some ⟨VaesBlocks.encryptBlocksF_correct, VaesBlocks.encryptBlocks_ctP,
    AesNi.Key.expandKey3_correct, AesNi.Key.expandKey3_ct⟩
  suffix := "_vaes"
  features := ["aes", "avx", "avx2", "vaes"]
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
