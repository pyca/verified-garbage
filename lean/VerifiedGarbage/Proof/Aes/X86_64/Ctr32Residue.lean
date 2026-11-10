module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Spec.Cmac.Contract
public meta import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public meta import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi
public meta import VerifiedGarbage.Impl.StackScratch.X86_64
public meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
public meta import VerifiedGarbage.Proof.Aes.X86_64.Variant

-- separate module: the residue analyses that `Variants/AesCtr32/X86_64.lean` and
-- `Variants/CmacAesUpdate/X86_64.lean` give the implementations, without importing the
-- analysis into every proof over them

/-!
# The residue analyses of the functions over each implementation of `vg_aes_ctr32` on x86-64

`vg_cmac_aes_finish` over each implementation of `vg_aes_ctr32`,
`vg_aes_gcm_init` over the AES-NI and VAES ones, and `vg_cmac_aes_absorb`
over `vg_cmac_aes_update_aesni`, analysed for what they may leave of secrets
(`X86_64.RScrub.Analysed`), which the variants give those implementations
(`Aes.X86_64.Ctr32Impl.cmacFinishRes`, `Aes.X86_64.Ctr32Impl.gcmInitRes`,
`CmacAes.X86_64.UpdateImpl.absorbRes`).
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.X86_64
materialize_code finishScalar := Impl.StackScratch.X86_64.withStackScratch 2312 .r8
  (Impl.CmacAes.Stream.X86_64.finish Impl.Aes.X86_64.Ctr32.scalar "")
materialize_code finishAesni := Impl.StackScratch.X86_64.withStackScratch 2312 .r8
  (Impl.CmacAes.Stream.X86_64.finish Impl.Aes.X86_64.Ctr32.aesni "_aesni")
materialize_code finishVaes := Impl.StackScratch.X86_64.withStackScratch 2312 .r8
  (Impl.CmacAes.Stream.X86_64.finish Impl.Aes.X86_64.Ctr32.vaes "_vaes")
materialize_code absorbAesni := Impl.StackScratch.X86_64.withStackScratch 2312 .r9
  (Impl.CmacAes.Stream.X86_64.absorb ⟨"vg_cmac_aes_update" ++ "_aesni", Impl.CmacAes.X86_64.AesNi.update⟩)
end VG.Impl.CmacAes.Stream.X86_64

namespace VG.Impl.AesGcm.X86_64
materialize_code initAesni := VG.Proof.Aes.X86_64.gcmInitCode Impl.Aes.X86_64.Ctr32.aesni ["aes", "ssse3"]
materialize_code initVaes := VG.Proof.Aes.X86_64.gcmInitCode Impl.Aes.X86_64.Ctr32.vaes
  ["aes", "avx", "avx2", "ssse3", "vaes"]
end VG.Impl.AesGcm.X86_64

namespace VG.Proof.Aes.X86_64.Ctr32Residue

open VG.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Aes.X86_64

def finishScalarKs : List Nat := keep_for% Spec.Cmac.aesFinishApi.sig 2328
  (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.scalar "")) []

theorem finishScalar_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.aesFinishApi.sig 2328 [])
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.scalar "")) h).any
      (RScrub.resOkB · 2328 finishScalarKs (Impl.Scrub.X86_64.chunks 2328)) = true :=
  RScrub.Analysed.ok_of finishScalarKs (by taint_decide)

def finishAesniKs : List Nat := keep_for% Spec.Cmac.aesFinishApi.sig 2328
  (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.aesni "_aesni")) []

theorem finishAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.aesFinishApi.sig 2328 [])
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.aesni "_aesni")) h).any
      (RScrub.resOkB · 2328 finishAesniKs (Impl.Scrub.X86_64.chunks 2328)) = true :=
  RScrub.Analysed.ok_of finishAesniKs (by taint_decide)

def finishVaesKs : List Nat := keep_for% Spec.Cmac.aesFinishApi.sig 2328
  (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.vaes "_vaes")) []

theorem finishVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.aesFinishApi.sig 2328 [])
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.vaes "_vaes")) h).any
      (RScrub.resOkB · 2328 finishVaesKs (Impl.Scrub.X86_64.chunks 2328)) = true :=
  RScrub.Analysed.ok_of finishVaesKs (by taint_decide)

def absorbAesniKs : List Nat := keep_for% Spec.Cmac.aesAbsorbApi.sig 2328
  (Impl.StackScratch.X86_64.withStackScratch 2312 .r9
    (Impl.CmacAes.Stream.X86_64.absorb ⟨"vg_cmac_aes_update" ++ "_aesni", Impl.CmacAes.X86_64.AesNi.update⟩)) []

theorem absorbAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.aesAbsorbApi.sig 2328 [])
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r9
        (Impl.CmacAes.Stream.X86_64.absorb ⟨"vg_cmac_aes_update" ++ "_aesni", Impl.CmacAes.X86_64.AesNi.update⟩)) h).any
      (RScrub.resOkB · 2328 absorbAesniKs (Impl.Scrub.X86_64.chunks 2328)) = true :=
  RScrub.Analysed.ok_of absorbAesniKs (by taint_decide)

/-- The analysis of `vg_cmac_aes_finish`. -/
def finishScalar : RScrub.Analysed Spec.Cmac.aesFinishApi.sig 2328 []
    (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.scalar "")) :=
  ⟨finishScalarKs, finishScalar_ok⟩

/-- The analysis of `vg_cmac_aes_finish_aesni`. -/
def finishAesni : RScrub.Analysed Spec.Cmac.aesFinishApi.sig 2328 []
    (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.aesni "_aesni")) :=
  ⟨finishAesniKs, finishAesni_ok⟩

/-- The analysis of `vg_cmac_aes_finish_vaes`. -/
def finishVaes : RScrub.Analysed Spec.Cmac.aesFinishApi.sig 2328 []
    (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish Ctr32.vaes "_vaes")) :=
  ⟨finishVaesKs, finishVaes_ok⟩

/-- The analysis of `vg_cmac_aes_absorb_aesni`. -/
def absorbAesni : RScrub.Analysed Spec.Cmac.aesAbsorbApi.sig 2328 []
    (Impl.StackScratch.X86_64.withStackScratch 2312 .r9
      (Impl.CmacAes.Stream.X86_64.absorb ⟨"vg_cmac_aes_update" ++ "_aesni", Impl.CmacAes.X86_64.AesNi.update⟩)) :=
  ⟨absorbAesniKs, absorbAesni_ok⟩

def gcmAesniKs : List Nat := keep_for% Spec.Gcm.initApi.sig 2576 (gcmInitCode Ctr32.aesni ["aes", "ssse3"]) []

theorem gcmAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.initApi.sig 2576 [])
      (gcmInitCode Ctr32.aesni ["aes", "ssse3"]) h).any
      (RScrub.resOkB · 2576 gcmAesniKs (Impl.Scrub.X86_64.chunks 2576)) = true :=
  RScrub.Analysed.ok_of gcmAesniKs (by taint_decide)

def gcmVaesKs : List Nat := keep_for% Spec.Gcm.initApi.sig 2576 (gcmInitCode Ctr32.vaes ["aes", "avx", "avx2", "ssse3", "vaes"]) []

theorem gcmVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.initApi.sig 2576 [])
      (gcmInitCode Ctr32.vaes ["aes", "avx", "avx2", "ssse3", "vaes"]) h).any
      (RScrub.resOkB · 2576 gcmVaesKs (Impl.Scrub.X86_64.chunks 2576)) = true :=
  RScrub.Analysed.ok_of gcmVaesKs (by taint_decide)

/-- The analysis of `vg_aes_gcm_init_aesni`. -/
def gcmAesni : RScrub.Analysed Spec.Gcm.initApi.sig 2576 [] (gcmInitCode Ctr32.aesni ["aes", "ssse3"]) :=
  ⟨gcmAesniKs, gcmAesni_ok⟩

/-- The analysis of `vg_aes_gcm_init_vaes`. -/
def gcmVaes : RScrub.Analysed Spec.Gcm.initApi.sig 2576 [] (gcmInitCode Ctr32.vaes ["aes", "avx", "avx2", "ssse3", "vaes"]) :=
  ⟨gcmVaesKs, gcmVaes_ok⟩

end VG.Proof.Aes.X86_64.Ctr32Residue
