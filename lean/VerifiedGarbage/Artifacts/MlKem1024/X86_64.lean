module

public import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
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
    notes := Artifacts.MlKem.X86_64.kpkeNotes
    code := Impl.MlKem.X86_64.kpkeKg Impl.MlKem1024.X86_64.kem1024 .avx2 Impl.MlKem.X86_64.keygenMul16Y
    verified := Proof.MlKem1024.X86_64.kpkeKg1024Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem1024.kpkeEncryptApi.artifact X86_64.target {
    notes := Artifacts.MlKem.X86_64.kpkeNotes
    code := Impl.MlKem.X86_64.kpkeEnc Impl.MlKem1024.X86_64.kem1024 .avx2 Impl.MlKem.X86_64.encryptMul16Y
    verified := Proof.MlKem1024.X86_64.kpkeEnc1024Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem1024.kpkeDecryptApi.artifact X86_64.target {
    notes := Artifacts.MlKem.X86_64.kpkeNotes
    code := Impl.MlKem.X86_64.kpkeDec Impl.MlKem1024.X86_64.kem1024 .avx2 Impl.MlKem.X86_64.Kpke16.dmInnerY
    verified := Proof.MlKem1024.X86_64.kpkeDec1024Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem1024.encryptMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.encryptMul .sse 4
    verified := Proof.MlKem.X86_64.encMulSse4_verified },
  Spec.MlKem1024.decryptMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.decryptMul .sse 4
    verified := Proof.MlKem.X86_64.decMulSse4_verified },
  Spec.MlKem1024.keygenMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts` and \
        `vg_mlkem_add` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once around all its \
        multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the \
        caller's MXCSR back before returning."]
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
    verified := Proof.MlKem1024.X86_64.checkEk1024_verified }]

end VG.Artifacts.MlKem1024.X86_64
