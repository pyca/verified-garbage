module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
public import VerifiedGarbage.Proof.MlKem.X86_64.Sample16
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified16
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-KEM (FIPS 203) on x86-64: the polynomial primitives -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact := [
  Spec.MlKem.kpkeEncryptApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.kpkeEnc Impl.MlKem.X86_64.kem768 .avx2 Impl.MlKem.X86_64.encryptMul16Y
    verified := Proof.MlKem.X86_64.kpkeEnc768Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.kpkeDecryptApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.kpkeDec Impl.MlKem.X86_64.kem768 .avx2 Impl.MlKem.X86_64.Kpke16.dmInnerY
    verified := Proof.MlKem.X86_64.kpkeDec768Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.sampleNTT16Api.artifact X86_64.target {
    code := Impl.MlKem.X86_64.sampleNTT16
    stack := 16
    verified := Proof.MlKem.X86_64.sample16_verified },
  Spec.MlKem.sampleNTT4_16Api.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 false true
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_16_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.sampleNTT4_16Api.artifact X86_64.target {
    suffix := "_avx512"
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 true true
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_16_verified
    features := ["avx", "avx2", "avx512f", "avx512vl"] },
  Spec.MlKem.cbd2_16Api.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlKem.X86_64.cbd2_16Avx2
    verified := Proof.MlKem.X86_64.cbd2_16Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.encryptMulApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.encryptMul .sse 3
    verified := Proof.MlKem.X86_64.encMulSse3_verified },
  Spec.MlKem.decryptMulApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.decryptMul .sse 3
    verified := Proof.MlKem.X86_64.decMulSse3_verified },
  Spec.MlKem.keygenMulApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.keygenMul .sse 3
    verified := Proof.MlKem.X86_64.kgMulSse3_verified },
  Spec.MlKem.addApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.add
    verified := Proof.MlKem.X86_64.add_verified },
  Spec.MlKem.subApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.sub
    verified := Proof.MlKem.X86_64.sub_verified },
  Spec.MlKem.sampleNTTApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.sampleNTT
    stack := 16
    verified := Proof.MlKem.X86_64.sample_verified },
  Spec.MlKem.encode12Api.artifact X86_64.target {
    code := Impl.MlKem.X86_64.encode12
    verified := Proof.MlKem.X86_64.encode12_verified },
  Spec.MlKem.decode12Api.artifact X86_64.target {
    code := Impl.MlKem.X86_64.decode12
    verified := Proof.MlKem.X86_64.decode12_verified },
  Spec.MlKem.cbd2Api.artifact X86_64.target {
    code := Impl.MlKem.X86_64.cbd2
    verified := Proof.MlKem.X86_64.cbd2_verified },
  Spec.MlKem.compressEncodeApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.compressEncode
    verified := Proof.MlKem.X86_64.compressEncode_verified },
  Spec.MlKem.decodeDecompressApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.decodeDecompress
    verified := Proof.MlKem.X86_64.decodeDecompress_verified },
  Spec.MlKem.checkEkApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.checkEk
    verified := Proof.MlKem.X86_64.checkEk_verified },
  Spec.MlKem.checkEkApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlKem.X86_64.checkEkAvx2
    verified := Proof.MlKem.X86_64.checkEkAvx2_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.sampleNTT4Api.artifact X86_64.target {
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_scalar_verified }]

end VG.Artifacts.MlKem.X86_64
