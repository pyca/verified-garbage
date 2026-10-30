module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeKgV
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeDecV
public import VerifiedGarbage.Artifacts.MlKem.X86_64
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on x86-64: the polynomial primitives -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.X86_64

def artifacts : List Artifact := [
  Spec.MlKem1024.kpkeKeyGenApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.kpkeKg Impl.MlKem1024.X86_64.kem1024 .avx2 Impl.MlKem.X86_64.keygenMul16Y
    verified := Proof.MlKem1024.X86_64.kpkeKg1024Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem1024.kpkeEncryptApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.kpkeEnc Impl.MlKem1024.X86_64.kem1024 .avx2 Impl.MlKem.X86_64.encryptMul16Y
    verified := Proof.MlKem1024.X86_64.kpkeEnc1024Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem1024.kpkeDecryptApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.kpkeDec Impl.MlKem1024.X86_64.kem1024 .avx2 Impl.MlKem.X86_64.Kpke16.dmInnerY
    verified := Proof.MlKem1024.X86_64.kpkeDec1024Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem1024.encryptMulApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.encryptMul .sse 4
    verified := Proof.MlKem.X86_64.encMulSse4_verified },
  Spec.MlKem1024.decryptMulApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.decryptMul .sse 4
    verified := Proof.MlKem.X86_64.decMulSse4_verified },
  Spec.MlKem1024.keygenMulApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.keygenMul .sse 4
    verified := Proof.MlKem.X86_64.kgMulSse4_verified },
  Spec.MlKem1024.compressEncodeApi.artifact X86_64.target {
    code := Impl.MlKem1024.X86_64.compressEncode1024
    verified := Proof.MlKem1024.X86_64.compressEncode1024_verified },
  Spec.MlKem1024.decodeDecompressApi.artifact X86_64.target {
    code := Impl.MlKem1024.X86_64.decodeDecompress1024
    verified := Proof.MlKem1024.X86_64.decodeDecompress1024_verified },
  Spec.MlKem1024.checkEkApi.artifact X86_64.target {
    code := Impl.MlKem1024.X86_64.checkEk1024
    verified := Proof.MlKem1024.X86_64.checkEk1024_verified },
  Spec.MlKem1024.checkEkApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlKem1024.X86_64.checkEk1024Avx2
    verified := Proof.MlKem1024.X86_64.checkEk1024Avx2_verified
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlKem1024.X86_64
