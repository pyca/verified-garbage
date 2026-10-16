module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on x86-64: the polynomial primitives -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.X86_64

def artifacts : List Artifact := [
  Spec.MlKem1024.encryptMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.encryptMul .sse 4
    verified := Proof.MlKem.X86_64.encMulSse4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlKem1024.encryptMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2`, `vg_mlkem_add_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 \
        registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.encryptMul .avx2 4
    verified := Proof.MlKem.X86_64.encMulAvx4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlKem1024.decryptMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.decryptMul .sse 4
    verified := Proof.MlKem.X86_64.decMulSse4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlKem1024.decryptMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2`, `vg_mlkem_add_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 \
        registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.decryptMul .avx2 4
    verified := Proof.MlKem.X86_64.decMulAvx4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlKem1024.keygenMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts` and \
        `vg_mlkem_add` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once around all its \
        multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the \
        caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.keygenMul .sse 4
    verified := Proof.MlKem.X86_64.kgMulSse4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlKem1024.keygenMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes with the code of `vg_mlkem_ntt_avx2` and \
        `vg_mlkem_multiply_ntts_avx2` inlined, on AVX2 registers, summing each row's products in 16-bit \
        words. It sets MXCSR to `0x1FBF` once around all its multiplications (Intel's mitigation of \
        MXCSR-configuration-dependent timing) and loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.keygenMul .avx2 4
    verified := Proof.MlKem.X86_64.kgMulAvx4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlKem1024.compressEncodeApi.artifact X86_64.target {
    code := Impl.MlKem1024.X86_64.compressEncode1024
    verified := Proof.MlKem1024.X86_64.compressEncode1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlKem1024.decodeDecompressApi.artifact X86_64.target {
    code := Impl.MlKem1024.X86_64.decodeDecompress1024
    verified := Proof.MlKem1024.X86_64.decodeDecompress1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlKem1024.checkEkApi.artifact X86_64.target {
    code := Impl.MlKem1024.X86_64.checkEk1024
    verified := Proof.MlKem1024.X86_64.checkEk1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlKem1024.X86_64
