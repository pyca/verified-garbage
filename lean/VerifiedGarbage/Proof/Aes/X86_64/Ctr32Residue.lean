module

public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public meta import VerifiedGarbage.Proof.Aes.X86_64.Variant
public meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit

-- separate module: the residue analyses that `Variants/AesCtr32/X86_64.lean` gives the
-- implementations, without importing the analysis into every proof over them

/-!
# The residue analyses of the functions over each implementation of `vg_aes_ctr32` on x86-64

`vg_aes_gcm_init` and `vg_cmac_aes_finish` over the AES-NI and VAES
implementations, with no working space for them (`Aes.X86_64.gcmInitCodeF`,
`Impl.CmacAes.Stream.X86_64.finishF`), analysed for what they may leave of
secrets (`X86_64.RScrub.Analysed`), which the variants give those
implementations (`Aes.X86_64.Ctr32Impl.gcmInitRes`, `cmacFinishRes`).
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64
materialize_code initAesniF := VG.Proof.Aes.X86_64.gcmInitCodeF Impl.Aes.X86_64.Ctr32.aesni
materialize_code initVaesF := VG.Proof.Aes.X86_64.gcmInitCodeF Impl.Aes.X86_64.Ctr32.vaes
end VG.Impl.AesGcm.X86_64

namespace VG.Impl.CmacAes.Stream.X86_64
materialize_code finishAesniF := Impl.StackScratch.X86_64.withStackScratch 24 .r8
  (Impl.CmacAes.Stream.X86_64.finishF Impl.Aes.X86_64.Ctr32.aesni "_aesni")
materialize_code finishVaesF := Impl.StackScratch.X86_64.withStackScratch 24 .r8
  (Impl.CmacAes.Stream.X86_64.finishF Impl.Aes.X86_64.Ctr32.vaes "_vaes")
end VG.Impl.CmacAes.Stream.X86_64

namespace VG.Proof.Aes.X86_64.Ctr32Residue

open VG.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Aes.X86_64

def gcmAesniKs : List Nat := keep_for% Spec.Gcm.initApi.sig 192 (gcmInitCodeF Ctr32.aesni) []

theorem gcmAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.initApi.sig 192 []) (gcmInitCodeF Ctr32.aesni) h).any
      (RScrub.resOkB · 192 gcmAesniKs (Impl.Scrub.X86_64.chunks 192)) = true :=
  RScrub.Analysed.ok_of gcmAesniKs (by taint_decide)

def gcmVaesKs : List Nat := keep_for% Spec.Gcm.initApi.sig 192 (gcmInitCodeF Ctr32.vaes) []

theorem gcmVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.initApi.sig 192 []) (gcmInitCodeF Ctr32.vaes) h).any
      (RScrub.resOkB · 192 gcmVaesKs (Impl.Scrub.X86_64.chunks 192)) = true :=
  RScrub.Analysed.ok_of gcmVaesKs (by taint_decide)

/-- The analysis of `vg_aes_gcm_init_aesni`. -/
def gcmAesni : RScrub.Analysed Spec.Gcm.initApi.sig 192 [] (gcmInitCodeF Ctr32.aesni) :=
  ⟨gcmAesniKs, gcmAesni_ok⟩

/-- The analysis of `vg_aes_gcm_init_vaes`. -/
def gcmVaes : RScrub.Analysed Spec.Gcm.initApi.sig 192 [] (gcmInitCodeF Ctr32.vaes) :=
  ⟨gcmVaesKs, gcmVaes_ok⟩

def finishAesniKs : List Nat := keep_for% Spec.Cmac.aesFinishApi.sig 40
  (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF Ctr32.aesni "_aesni")) []

theorem finishAesni_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.aesFinishApi.sig 40 [])
      (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF Ctr32.aesni "_aesni")) h).any
      (RScrub.resOkB · 40 finishAesniKs (Impl.Scrub.X86_64.chunks 40)) = true :=
  RScrub.Analysed.ok_of finishAesniKs (by taint_decide)

def finishVaesKs : List Nat := keep_for% Spec.Cmac.aesFinishApi.sig 40
  (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF Ctr32.vaes "_vaes")) []

theorem finishVaes_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.aesFinishApi.sig 40 [])
      (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF Ctr32.vaes "_vaes")) h).any
      (RScrub.resOkB · 40 finishVaesKs (Impl.Scrub.X86_64.chunks 40)) = true :=
  RScrub.Analysed.ok_of finishVaesKs (by taint_decide)

/-- The analysis of `vg_cmac_aes_finish_aesni`. -/
def finishAesni : RScrub.Analysed Spec.Cmac.aesFinishApi.sig 40 []
    (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF Ctr32.aesni "_aesni")) :=
  ⟨finishAesniKs, finishAesni_ok⟩

/-- The analysis of `vg_cmac_aes_finish_vaes`. -/
def finishVaes : RScrub.Analysed Spec.Cmac.aesFinishApi.sig 40 []
    (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF Ctr32.vaes "_vaes")) :=
  ⟨finishVaesKs, finishVaes_ok⟩

end VG.Proof.Aes.X86_64.Ctr32Residue
