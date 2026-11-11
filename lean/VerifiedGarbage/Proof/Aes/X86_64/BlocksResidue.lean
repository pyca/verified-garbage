module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Impl.AesCfb8.X86_64
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Impl.AesCfb.X86_64
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Impl.AesOfb.X86_64
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
public meta import VerifiedGarbage.Spec.Cfb.Contract
public meta import VerifiedGarbage.Impl.AesCfb.X86_64
public meta import VerifiedGarbage.Spec.Ofb.Contract
public meta import VerifiedGarbage.Impl.AesOfb.X86_64
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
`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`, AES-CFB128's
`vg_aes_cfb128_encrypt` and `vg_aes_cfb128_decrypt`, `vg_aes_ofb`,
`vg_aes_ecb_encrypt` (the
code of `vg_aes_encrypt_blocks` itself) and `vg_aes_ocb_init`, with no
working space for the functions it calls (`Aes.X86_64.ocbInitCodeF`).
`Variants/AesBlocks/X86_64.lean` gives them to those implementations
(`BlocksImpl.cfb8EncRes`, `BlocksImpl.cfb8DecRes`, `BlocksImpl.cfbEncRes`,
`BlocksImpl.cfbDecRes`, `BlocksImpl.ofbRes`, `BlocksImpl.ecbEncRes`,
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

/-! ## AES-CFB128 and AES-OFB -/

def cfbEncAesniKs : List Nat := keep_for% Spec.Cfb.aesEncryptApi.sig 8 (Impl.AesCfb.X86_64.encrypt Blocks.encAesni) []

theorem cfbEncAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb.aesEncryptApi.sig 8 [])
      (Impl.AesCfb.X86_64.encrypt Blocks.encAesni) h).any
      (RScrub.resOkB · 8 cfbEncAesniKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of cfbEncAesniKs (by taint_decide)

/-- `cfbEncAesniKs`, with its analysis. -/
def cfbEncAesni : RScrub.Analysed Spec.Cfb.aesEncryptApi.sig 8 [] (Impl.AesCfb.X86_64.encrypt Blocks.encAesni) := ⟨cfbEncAesniKs, cfbEncAesni_ok⟩

def cfbEncVaesKs : List Nat := keep_for% Spec.Cfb.aesEncryptApi.sig 8 (Impl.AesCfb.X86_64.encrypt Blocks.encVaes) []

theorem cfbEncVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb.aesEncryptApi.sig 8 [])
      (Impl.AesCfb.X86_64.encrypt Blocks.encVaes) h).any
      (RScrub.resOkB · 8 cfbEncVaesKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of cfbEncVaesKs (by taint_decide)

/-- `cfbEncVaesKs`, with its analysis. -/
def cfbEncVaes : RScrub.Analysed Spec.Cfb.aesEncryptApi.sig 8 [] (Impl.AesCfb.X86_64.encrypt Blocks.encVaes) := ⟨cfbEncVaesKs, cfbEncVaes_ok⟩

def cfbDecAesniKs : List Nat := keep_for% Spec.Cfb.aesDecryptApi.sig 8 (Impl.AesCfb.X86_64.decrypt Blocks.encAesni) []

theorem cfbDecAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb.aesDecryptApi.sig 8 [])
      (Impl.AesCfb.X86_64.decrypt Blocks.encAesni) h).any
      (RScrub.resOkB · 8 cfbDecAesniKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of cfbDecAesniKs (by taint_decide)

/-- `cfbDecAesniKs`, with its analysis. -/
def cfbDecAesni : RScrub.Analysed Spec.Cfb.aesDecryptApi.sig 8 [] (Impl.AesCfb.X86_64.decrypt Blocks.encAesni) := ⟨cfbDecAesniKs, cfbDecAesni_ok⟩

def cfbDecVaesKs : List Nat := keep_for% Spec.Cfb.aesDecryptApi.sig 8 (Impl.AesCfb.X86_64.decrypt Blocks.encVaes) []

theorem cfbDecVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cfb.aesDecryptApi.sig 8 [])
      (Impl.AesCfb.X86_64.decrypt Blocks.encVaes) h).any
      (RScrub.resOkB · 8 cfbDecVaesKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of cfbDecVaesKs (by taint_decide)

/-- `cfbDecVaesKs`, with its analysis. -/
def cfbDecVaes : RScrub.Analysed Spec.Cfb.aesDecryptApi.sig 8 [] (Impl.AesCfb.X86_64.decrypt Blocks.encVaes) := ⟨cfbDecVaesKs, cfbDecVaes_ok⟩

def ofbAesniKs : List Nat := keep_for% Spec.Ofb.aesApi.sig 8 (Impl.AesOfb.X86_64.crypt Blocks.encAesni) []

theorem ofbAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ofb.aesApi.sig 8 [])
      (Impl.AesOfb.X86_64.crypt Blocks.encAesni) h).any
      (RScrub.resOkB · 8 ofbAesniKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of ofbAesniKs (by taint_decide)

/-- `ofbAesniKs`, with its analysis. -/
def ofbAesni : RScrub.Analysed Spec.Ofb.aesApi.sig 8 [] (Impl.AesOfb.X86_64.crypt Blocks.encAesni) := ⟨ofbAesniKs, ofbAesni_ok⟩

def ofbVaesKs : List Nat := keep_for% Spec.Ofb.aesApi.sig 8 (Impl.AesOfb.X86_64.crypt Blocks.encVaes) []

theorem ofbVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ofb.aesApi.sig 8 [])
      (Impl.AesOfb.X86_64.crypt Blocks.encVaes) h).any
      (RScrub.resOkB · 8 ofbVaesKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of ofbVaesKs (by taint_decide)

/-- `ofbVaesKs`, with its analysis. -/
def ofbVaes : RScrub.Analysed Spec.Ofb.aesApi.sig 8 [] (Impl.AesOfb.X86_64.crypt Blocks.encVaes) := ⟨ofbVaesKs, ofbVaes_ok⟩

end VG.Proof.Aes.X86_64.BlocksResidue

namespace VG.Impl.AesOcb.X86_64
materialize_code initAesniF := Impl.StackScratch.X86_64.withStackScratch 32 .rcx
  (Impl.AesOcb.X86_64.init ⟨Impl.Aes.X86_64.Blocks.encAesni, Impl.Aes.X86_64.Blocks.decAesni,
    Impl.Aes.X86_64.ExpandKey.aesni⟩)
materialize_code initVaesF := Impl.StackScratch.X86_64.withStackScratch 32 .rcx
  (Impl.AesOcb.X86_64.init ⟨Impl.Aes.X86_64.Blocks.encVaes, Impl.Aes.X86_64.Blocks.decVaes,
    Impl.Aes.X86_64.ExpandKey.aesni⟩)
end VG.Impl.AesOcb.X86_64

namespace VG.Proof.Aes.X86_64.BlocksResidue

open VG.X86_64 VG.Impl.Aes.X86_64

/-! ## AES-OCB's key setup -/

def ocbAesniKs : List Nat := keep_for% Spec.Ocb.initApi.sig 40
  (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encAesni, Blocks.decAesni, ExpandKey.aesni⟩)) []

theorem ocbAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ocb.initApi.sig 40 [])
      (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encAesni, Blocks.decAesni, ExpandKey.aesni⟩)) h).any
      (RScrub.resOkB · 40 ocbAesniKs (Impl.Scrub.X86_64.chunks 40)) = true :=
  RScrub.Analysed.ok_of ocbAesniKs (by taint_decide)

def ocbVaesKs : List Nat := keep_for% Spec.Ocb.initApi.sig 40
  (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encVaes, Blocks.decVaes, ExpandKey.aesni⟩)) []

theorem ocbVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ocb.initApi.sig 40 [])
      (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨Blocks.encVaes, Blocks.decVaes, ExpandKey.aesni⟩)) h).any
      (RScrub.resOkB · 40 ocbVaesKs (Impl.Scrub.X86_64.chunks 40)) = true :=
  RScrub.Analysed.ok_of ocbVaesKs (by taint_decide)

/-- The analysis of `vg_aes_ocb_init_aesni`. -/
def ocbAesni : RScrub.Analysed Spec.Ocb.initApi.sig 40 []
    (Impl.StackScratch.X86_64.withStackScratch 32 .rcx
      (Impl.AesOcb.X86_64.init ⟨Blocks.encAesni, Blocks.decAesni, ExpandKey.aesni⟩)) := ⟨ocbAesniKs, ocbAesni_ok⟩

/-- The analysis of `vg_aes_ocb_init_vaes`. -/
def ocbVaes : RScrub.Analysed Spec.Ocb.initApi.sig 40 []
    (Impl.StackScratch.X86_64.withStackScratch 32 .rcx
      (Impl.AesOcb.X86_64.init ⟨Blocks.encVaes, Blocks.decVaes, ExpandKey.aesni⟩)) := ⟨ocbVaesKs, ocbVaes_ok⟩

end VG.Proof.Aes.X86_64.BlocksResidue
