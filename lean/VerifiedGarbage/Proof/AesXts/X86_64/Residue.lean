module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.AesXts.X86_64.Variant

-- separate module: the residue analyses that `Variants/AesXts/X86_64.lean` gives the
-- implementations, without importing the analysis into the proofs of the data-unit functions

/-!
# The residue analyses of the XTS-AES data-unit functions on x86-64

The data-unit functions generic over the implementations of the whole-block
functions (`AesXts.X86_64.XtsImpl`) that the residue analysis handles, over
the one-pass implementations, analysed for what they may leave of secrets
(`X86_64.RScrub.Analysed`): `vg_aes_xts_encrypt_unit`,
`vg_aes_xts_decrypt_unit` and their out-of-place counterparts.
`Variants/AesXts/X86_64.lean` gives them to those implementations
(`XtsImpl.encUnitRes`, `XtsImpl.decUnitRes`, `XtsImpl.encUnitToRes`,
`XtsImpl.decUnitToRes`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Residue

open VG.X86_64 VG.Proof.AesXts.X86_64

def encUnitVaesVpclmulAvx512Ks : List Nat := keep_for% Spec.Xts.aesEncryptUnitApi.sig 16
    (Impl.AesXts.X86_64Unit.encrypt XtsImpl.vaesVpclmulAvx512.xts) []

theorem encUnitVaesVpclmulAvx512_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesEncryptUnitApi.sig 16 [])
      (Impl.AesXts.X86_64Unit.encrypt XtsImpl.vaesVpclmulAvx512.xts) h).any
      (RScrub.resOkB · 16 encUnitVaesVpclmulAvx512Ks (Impl.Scrub.X86_64.chunks 16)) = true :=
  RScrub.Analysed.ok_of encUnitVaesVpclmulAvx512Ks (by taint_decide)

/-- The analysis of `vg_aes_xts_encrypt_unit_vaes_vpclmul_avx512`. -/
def encUnitVaesVpclmulAvx512 : RScrub.Analysed Spec.Xts.aesEncryptUnitApi.sig 16 []
    (Impl.AesXts.X86_64Unit.encrypt XtsImpl.vaesVpclmulAvx512.xts) :=
  ⟨encUnitVaesVpclmulAvx512Ks, encUnitVaesVpclmulAvx512_ok⟩

def decUnitVaesVpclmulAvx512Ks : List Nat := keep_for% Spec.Xts.aesDecryptUnitApi.sig 16
    (Impl.AesXts.X86_64Unit.decrypt XtsImpl.vaesVpclmulAvx512.xts) []

theorem decUnitVaesVpclmulAvx512_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesDecryptUnitApi.sig 16 [])
      (Impl.AesXts.X86_64Unit.decrypt XtsImpl.vaesVpclmulAvx512.xts) h).any
      (RScrub.resOkB · 16 decUnitVaesVpclmulAvx512Ks (Impl.Scrub.X86_64.chunks 16)) = true :=
  RScrub.Analysed.ok_of decUnitVaesVpclmulAvx512Ks (by taint_decide)

/-- The analysis of `vg_aes_xts_decrypt_unit_vaes_vpclmul_avx512`. -/
def decUnitVaesVpclmulAvx512 : RScrub.Analysed Spec.Xts.aesDecryptUnitApi.sig 16 []
    (Impl.AesXts.X86_64Unit.decrypt XtsImpl.vaesVpclmulAvx512.xts) :=
  ⟨decUnitVaesVpclmulAvx512Ks, decUnitVaesVpclmulAvx512_ok⟩

def encUnitToVaesVpclmulAvx512Ks : List Nat := keep_for% Spec.Xts.aesEncryptUnitToApi.sig 24
    (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.vaesVpclmulAvx512.xts ⟨XtsImpl.vaesVpclmulAvx512.to.enc, XtsImpl.vaesVpclmulAvx512.to.dec⟩) []

theorem encUnitToVaesVpclmulAvx512_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesEncryptUnitToApi.sig 24 [])
      (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.vaesVpclmulAvx512.xts ⟨XtsImpl.vaesVpclmulAvx512.to.enc, XtsImpl.vaesVpclmulAvx512.to.dec⟩) h).any
      (RScrub.resOkB · 24 encUnitToVaesVpclmulAvx512Ks (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of encUnitToVaesVpclmulAvx512Ks (by taint_decide)

/-- The analysis of `vg_aes_xts_encrypt_unit_to_vaes_vpclmul_avx512`. -/
def encUnitToVaesVpclmulAvx512 : RScrub.Analysed Spec.Xts.aesEncryptUnitToApi.sig 24 []
    (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.vaesVpclmulAvx512.xts ⟨XtsImpl.vaesVpclmulAvx512.to.enc, XtsImpl.vaesVpclmulAvx512.to.dec⟩) :=
  ⟨encUnitToVaesVpclmulAvx512Ks, encUnitToVaesVpclmulAvx512_ok⟩

def decUnitToVaesVpclmulAvx512Ks : List Nat := keep_for% Spec.Xts.aesDecryptUnitToApi.sig 24
    (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.vaesVpclmulAvx512.xts ⟨XtsImpl.vaesVpclmulAvx512.to.enc, XtsImpl.vaesVpclmulAvx512.to.dec⟩) []

theorem decUnitToVaesVpclmulAvx512_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesDecryptUnitToApi.sig 24 [])
      (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.vaesVpclmulAvx512.xts ⟨XtsImpl.vaesVpclmulAvx512.to.enc, XtsImpl.vaesVpclmulAvx512.to.dec⟩) h).any
      (RScrub.resOkB · 24 decUnitToVaesVpclmulAvx512Ks (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of decUnitToVaesVpclmulAvx512Ks (by taint_decide)

/-- The analysis of `vg_aes_xts_decrypt_unit_to_vaes_vpclmul_avx512`. -/
def decUnitToVaesVpclmulAvx512 : RScrub.Analysed Spec.Xts.aesDecryptUnitToApi.sig 24 []
    (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.vaesVpclmulAvx512.xts ⟨XtsImpl.vaesVpclmulAvx512.to.enc, XtsImpl.vaesVpclmulAvx512.to.dec⟩) :=
  ⟨decUnitToVaesVpclmulAvx512Ks, decUnitToVaesVpclmulAvx512_ok⟩

def encUnitVaesVpclmulKs : List Nat := keep_for% Spec.Xts.aesEncryptUnitApi.sig 16
    (Impl.AesXts.X86_64Unit.encrypt XtsImpl.vaesVpclmul.xts) []

theorem encUnitVaesVpclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesEncryptUnitApi.sig 16 [])
      (Impl.AesXts.X86_64Unit.encrypt XtsImpl.vaesVpclmul.xts) h).any
      (RScrub.resOkB · 16 encUnitVaesVpclmulKs (Impl.Scrub.X86_64.chunks 16)) = true :=
  RScrub.Analysed.ok_of encUnitVaesVpclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_encrypt_unit_vaes_vpclmul`. -/
def encUnitVaesVpclmul : RScrub.Analysed Spec.Xts.aesEncryptUnitApi.sig 16 []
    (Impl.AesXts.X86_64Unit.encrypt XtsImpl.vaesVpclmul.xts) :=
  ⟨encUnitVaesVpclmulKs, encUnitVaesVpclmul_ok⟩

def decUnitVaesVpclmulKs : List Nat := keep_for% Spec.Xts.aesDecryptUnitApi.sig 16
    (Impl.AesXts.X86_64Unit.decrypt XtsImpl.vaesVpclmul.xts) []

theorem decUnitVaesVpclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesDecryptUnitApi.sig 16 [])
      (Impl.AesXts.X86_64Unit.decrypt XtsImpl.vaesVpclmul.xts) h).any
      (RScrub.resOkB · 16 decUnitVaesVpclmulKs (Impl.Scrub.X86_64.chunks 16)) = true :=
  RScrub.Analysed.ok_of decUnitVaesVpclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_decrypt_unit_vaes_vpclmul`. -/
def decUnitVaesVpclmul : RScrub.Analysed Spec.Xts.aesDecryptUnitApi.sig 16 []
    (Impl.AesXts.X86_64Unit.decrypt XtsImpl.vaesVpclmul.xts) :=
  ⟨decUnitVaesVpclmulKs, decUnitVaesVpclmul_ok⟩

def encUnitToVaesVpclmulKs : List Nat := keep_for% Spec.Xts.aesEncryptUnitToApi.sig 24
    (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.vaesVpclmul.xts ⟨XtsImpl.vaesVpclmul.to.enc, XtsImpl.vaesVpclmul.to.dec⟩) []

theorem encUnitToVaesVpclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesEncryptUnitToApi.sig 24 [])
      (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.vaesVpclmul.xts ⟨XtsImpl.vaesVpclmul.to.enc, XtsImpl.vaesVpclmul.to.dec⟩) h).any
      (RScrub.resOkB · 24 encUnitToVaesVpclmulKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of encUnitToVaesVpclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_encrypt_unit_to_vaes_vpclmul`. -/
def encUnitToVaesVpclmul : RScrub.Analysed Spec.Xts.aesEncryptUnitToApi.sig 24 []
    (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.vaesVpclmul.xts ⟨XtsImpl.vaesVpclmul.to.enc, XtsImpl.vaesVpclmul.to.dec⟩) :=
  ⟨encUnitToVaesVpclmulKs, encUnitToVaesVpclmul_ok⟩

def decUnitToVaesVpclmulKs : List Nat := keep_for% Spec.Xts.aesDecryptUnitToApi.sig 24
    (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.vaesVpclmul.xts ⟨XtsImpl.vaesVpclmul.to.enc, XtsImpl.vaesVpclmul.to.dec⟩) []

theorem decUnitToVaesVpclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesDecryptUnitToApi.sig 24 [])
      (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.vaesVpclmul.xts ⟨XtsImpl.vaesVpclmul.to.enc, XtsImpl.vaesVpclmul.to.dec⟩) h).any
      (RScrub.resOkB · 24 decUnitToVaesVpclmulKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of decUnitToVaesVpclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_decrypt_unit_to_vaes_vpclmul`. -/
def decUnitToVaesVpclmul : RScrub.Analysed Spec.Xts.aesDecryptUnitToApi.sig 24 []
    (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.vaesVpclmul.xts ⟨XtsImpl.vaesVpclmul.to.enc, XtsImpl.vaesVpclmul.to.dec⟩) :=
  ⟨decUnitToVaesVpclmulKs, decUnitToVaesVpclmul_ok⟩

def encUnitAesniPclmulKs : List Nat := keep_for% Spec.Xts.aesEncryptUnitApi.sig 16
    (Impl.AesXts.X86_64Unit.encrypt XtsImpl.aesniPclmul.xts) []

theorem encUnitAesniPclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesEncryptUnitApi.sig 16 [])
      (Impl.AesXts.X86_64Unit.encrypt XtsImpl.aesniPclmul.xts) h).any
      (RScrub.resOkB · 16 encUnitAesniPclmulKs (Impl.Scrub.X86_64.chunks 16)) = true :=
  RScrub.Analysed.ok_of encUnitAesniPclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_encrypt_unit_aesni_pclmul`. -/
def encUnitAesniPclmul : RScrub.Analysed Spec.Xts.aesEncryptUnitApi.sig 16 []
    (Impl.AesXts.X86_64Unit.encrypt XtsImpl.aesniPclmul.xts) :=
  ⟨encUnitAesniPclmulKs, encUnitAesniPclmul_ok⟩

def decUnitAesniPclmulKs : List Nat := keep_for% Spec.Xts.aesDecryptUnitApi.sig 16
    (Impl.AesXts.X86_64Unit.decrypt XtsImpl.aesniPclmul.xts) []

theorem decUnitAesniPclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesDecryptUnitApi.sig 16 [])
      (Impl.AesXts.X86_64Unit.decrypt XtsImpl.aesniPclmul.xts) h).any
      (RScrub.resOkB · 16 decUnitAesniPclmulKs (Impl.Scrub.X86_64.chunks 16)) = true :=
  RScrub.Analysed.ok_of decUnitAesniPclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_decrypt_unit_aesni_pclmul`. -/
def decUnitAesniPclmul : RScrub.Analysed Spec.Xts.aesDecryptUnitApi.sig 16 []
    (Impl.AesXts.X86_64Unit.decrypt XtsImpl.aesniPclmul.xts) :=
  ⟨decUnitAesniPclmulKs, decUnitAesniPclmul_ok⟩

def encUnitToAesniPclmulKs : List Nat := keep_for% Spec.Xts.aesEncryptUnitToApi.sig 24
    (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.aesniPclmul.xts ⟨XtsImpl.aesniPclmul.to.enc, XtsImpl.aesniPclmul.to.dec⟩) []

theorem encUnitToAesniPclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesEncryptUnitToApi.sig 24 [])
      (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.aesniPclmul.xts ⟨XtsImpl.aesniPclmul.to.enc, XtsImpl.aesniPclmul.to.dec⟩) h).any
      (RScrub.resOkB · 24 encUnitToAesniPclmulKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of encUnitToAesniPclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_encrypt_unit_to_aesni_pclmul`. -/
def encUnitToAesniPclmul : RScrub.Analysed Spec.Xts.aesEncryptUnitToApi.sig 24 []
    (Impl.AesXts.X86_64UnitTo.encrypt XtsImpl.aesniPclmul.xts ⟨XtsImpl.aesniPclmul.to.enc, XtsImpl.aesniPclmul.to.dec⟩) :=
  ⟨encUnitToAesniPclmulKs, encUnitToAesniPclmul_ok⟩

def decUnitToAesniPclmulKs : List Nat := keep_for% Spec.Xts.aesDecryptUnitToApi.sig 24
    (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.aesniPclmul.xts ⟨XtsImpl.aesniPclmul.to.enc, XtsImpl.aesniPclmul.to.dec⟩) []

theorem decUnitToAesniPclmul_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Xts.aesDecryptUnitToApi.sig 24 [])
      (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.aesniPclmul.xts ⟨XtsImpl.aesniPclmul.to.enc, XtsImpl.aesniPclmul.to.dec⟩) h).any
      (RScrub.resOkB · 24 decUnitToAesniPclmulKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of decUnitToAesniPclmulKs (by taint_decide)

/-- The analysis of `vg_aes_xts_decrypt_unit_to_aesni_pclmul`. -/
def decUnitToAesniPclmul : RScrub.Analysed Spec.Xts.aesDecryptUnitToApi.sig 24 []
    (Impl.AesXts.X86_64UnitTo.decrypt XtsImpl.aesniPclmul.xts ⟨XtsImpl.aesniPclmul.to.enc, XtsImpl.aesniPclmul.to.dec⟩) :=
  ⟨decUnitToAesniPclmulKs, decUnitToAesniPclmul_ok⟩

end VG.Proof.AesXts.X86_64.Residue
