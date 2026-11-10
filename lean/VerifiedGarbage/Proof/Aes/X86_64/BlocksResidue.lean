module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Impl.AesCfb8.X86_64
public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Spec.AesEcb.Contract
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.AesOcb.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Spec.Cfb8.Contract
public meta import VerifiedGarbage.Impl.AesCfb8.X86_64
public meta import VerifiedGarbage.Impl.Aes.X86_64.Callee
public meta import VerifiedGarbage.Spec.AesEcb.Contract
public meta import VerifiedGarbage.Spec.Ocb.Contract
public meta import VerifiedGarbage.Impl.AesOcb.X86_64
public meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: the residue analyses that `Variants/AesBlocks/X86_64.lean` gives the
-- implementations, without importing the analysis into every proof of a mode over them

/-!
# The residue analyses of the AES modes over each implementation on x86-64

The functions generic over the implementations of `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks` (`Aes.X86_64.BlocksImpl`) that the residue
analysis handles over the AES-NI and VAES implementations, analysed for what
they may leave of secrets (`X86_64.RScrub.Analysed`): AES-CFB8's
`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`, `vg_aes_ecb_encrypt` (the
code of `vg_aes_encrypt_blocks` itself) and `vg_aes_ocb_init`.
`Variants/AesBlocks/X86_64.lean` gives them to those implementations
(`BlocksImpl.cfb8EncRes`, `BlocksImpl.cfb8DecRes`, `BlocksImpl.ecbEncRes`,
`BlocksImpl.ocbInitRes`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.BlocksResidue

open VG.X86_64 VG.Impl.Aes.X86_64

/-! ## AES-CFB8 -/

def encAesniKs : List Nat := keep_for% Spec.Cfb8.aesEncryptApi.sig 8 (Impl.AesCfb8.X86_64.encrypt Blocks.encAesni) []

theorem encAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb8.aesEncryptApi.sig 8 [])
      (Impl.AesCfb8.X86_64.encrypt Blocks.encAesni) h).any
      (RScrub.resOkB · 8 encAesniKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of encAesniKs (by taint_decide)

def encVaesKs : List Nat := keep_for% Spec.Cfb8.aesEncryptApi.sig 8 (Impl.AesCfb8.X86_64.encrypt Blocks.encVaes) []

theorem encVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb8.aesEncryptApi.sig 8 [])
      (Impl.AesCfb8.X86_64.encrypt Blocks.encVaes) h).any
      (RScrub.resOkB · 8 encVaesKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of encVaesKs (by taint_decide)

def decAesniKs : List Nat := keep_for% Spec.Cfb8.aesDecryptApi.sig 8 (Impl.AesCfb8.X86_64.decrypt Blocks.encAesni) []

theorem decAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb8.aesDecryptApi.sig 8 [])
      (Impl.AesCfb8.X86_64.decrypt Blocks.encAesni) h).any
      (RScrub.resOkB · 8 decAesniKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of decAesniKs (by taint_decide)

def decVaesKs : List Nat := keep_for% Spec.Cfb8.aesDecryptApi.sig 8 (Impl.AesCfb8.X86_64.decrypt Blocks.encVaes) []

theorem decVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb8.aesDecryptApi.sig 8 [])
      (Impl.AesCfb8.X86_64.decrypt Blocks.encVaes) h).any
      (RScrub.resOkB · 8 decVaesKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of decVaesKs (by taint_decide)

/-- The analysis of `vg_aes_cfb8_encrypt_aesni`. -/
def encAesni : RScrub.Analysed Spec.Cfb8.aesEncryptApi.sig 8 [] (Impl.AesCfb8.X86_64.encrypt Blocks.encAesni) :=
  ⟨encAesniKs, encAesni_ok⟩

/-- The analysis of `vg_aes_cfb8_encrypt_vaes`. -/
def encVaes : RScrub.Analysed Spec.Cfb8.aesEncryptApi.sig 8 [] (Impl.AesCfb8.X86_64.encrypt Blocks.encVaes) :=
  ⟨encVaesKs, encVaes_ok⟩

/-- The analysis of `vg_aes_cfb8_decrypt_aesni`. -/
def decAesni : RScrub.Analysed Spec.Cfb8.aesDecryptApi.sig 8 [] (Impl.AesCfb8.X86_64.decrypt Blocks.encAesni) :=
  ⟨decAesniKs, decAesni_ok⟩

/-- The analysis of `vg_aes_cfb8_decrypt_vaes`. -/
def decVaes : RScrub.Analysed Spec.Cfb8.aesDecryptApi.sig 8 [] (Impl.AesCfb8.X86_64.decrypt Blocks.encVaes) :=
  ⟨decVaesKs, decVaes_ok⟩


/-! ## AES-ECB encryption -/

def ecbAesniKs : List Nat := keep_for% Spec.AesEcb.encryptApi.sig 0 Blocks.encAesni.code []

theorem ecbAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.AesEcb.encryptApi.sig 0 []) Blocks.encAesni.code h).any
      (RScrub.resOkB · 0 ecbAesniKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of ecbAesniKs (by taint_decide)

def ecbVaesKs : List Nat := keep_for% Spec.AesEcb.encryptApi.sig 0 Blocks.encVaes.code []

theorem ecbVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.AesEcb.encryptApi.sig 0 []) Blocks.encVaes.code h).any
      (RScrub.resOkB · 0 ecbVaesKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of ecbVaesKs (by taint_decide)

/-- The analysis of `vg_aes_ecb_encrypt_aesni`. -/
def ecbAesni : RScrub.Analysed Spec.AesEcb.encryptApi.sig 0 [] Blocks.encAesni.code := ⟨ecbAesniKs, ecbAesni_ok⟩

/-- The analysis of `vg_aes_ecb_encrypt_vaes`. -/
def ecbVaes : RScrub.Analysed Spec.AesEcb.encryptApi.sig 0 [] Blocks.encVaes.code := ⟨ecbVaesKs, ecbVaes_ok⟩

/-! ## AES-OCB's key setup -/

end VG.Proof.Aes.X86_64.BlocksResidue

namespace VG.Impl.AesOcb.X86_64
materialize_code initAesni := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
  (Impl.AesOcb.X86_64.init ⟨Impl.Aes.X86_64.Blocks.encAesni, Impl.Aes.X86_64.Blocks.decAesni,
    Impl.Aes.X86_64.ExpandKey.aesni⟩)
materialize_code initVaes := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
  (Impl.AesOcb.X86_64.init ⟨Impl.Aes.X86_64.Blocks.encVaes, Impl.Aes.X86_64.Blocks.decVaes,
    Impl.Aes.X86_64.ExpandKey.aesni⟩)
end VG.Impl.AesOcb.X86_64

namespace VG.Proof.Aes.X86_64.BlocksResidue

open VG.X86_64 VG.Impl.Aes.X86_64

def ocbAesniKs : List Nat := keep_for% Spec.Ocb.initApi.sig 2576
  (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encAesni, Blocks.decAesni, ExpandKey.aesni⟩)) []

theorem ocbAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ocb.initApi.sig 2576 [])
      (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encAesni, Blocks.decAesni, ExpandKey.aesni⟩)) h).any
      (RScrub.resOkB · 2576 ocbAesniKs (Impl.Scrub.X86_64.chunks 2576)) = true :=
  RScrub.Analysed.ok_of ocbAesniKs (by taint_decide)

def ocbVaesKs : List Nat := keep_for% Spec.Ocb.initApi.sig 2576
  (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encVaes, Blocks.decVaes, ExpandKey.aesni⟩)) []

theorem ocbVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ocb.initApi.sig 2576 [])
      (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encVaes, Blocks.decVaes, ExpandKey.aesni⟩)) h).any
      (RScrub.resOkB · 2576 ocbVaesKs (Impl.Scrub.X86_64.chunks 2576)) = true :=
  RScrub.Analysed.ok_of ocbVaesKs (by taint_decide)

/-- The analysis of `vg_aes_ocb_init_aesni`. -/
def ocbAesni : RScrub.Analysed Spec.Ocb.initApi.sig 2576 []
    (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
      (Impl.AesOcb.X86_64.init ⟨Blocks.encAesni, Blocks.decAesni, ExpandKey.aesni⟩)) := ⟨ocbAesniKs, ocbAesni_ok⟩

/-- The analysis of `vg_aes_ocb_init_vaes`. -/
def ocbVaes : RScrub.Analysed Spec.Ocb.initApi.sig 2576 []
    (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
      (Impl.AesOcb.X86_64.init ⟨Blocks.encVaes, Blocks.decVaes, ExpandKey.aesni⟩)) := ⟨ocbVaesKs, ocbVaes_ok⟩

end VG.Proof.Aes.X86_64.BlocksResidue
