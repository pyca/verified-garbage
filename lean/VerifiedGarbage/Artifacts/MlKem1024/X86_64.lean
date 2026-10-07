import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV

/-! # ML-KEM-1024 (FIPS 203) on x86-64: the polynomial primitives -/

namespace VG.Artifacts.MlKem1024.X86_64

def artifacts : List Artifact := [
  { Spec.MlKem1024.decryptMulApi with
    target := X86_64.target
    doc := Spec.MlKem1024.decryptMulApi.doc
      (notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.decryptMul .sse 4
    contract := Spec.MlKem.decryptMulContract 4 X86_64.abi
    verified := Proof.MlKem.X86_64.decMulSse4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.decryptMulApi with
    name := Spec.MlKem1024.decryptMulApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem1024.decryptMulApi.doc
      (notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2`, `vg_mlkem_add_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 \
        registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.decryptMul .avx2 4
    contract := Spec.MlKem.decryptMulContract 4 X86_64.abi
    verified := Proof.MlKem.X86_64.decMulAvx4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlKem1024.compressEncodeApi with
    target := X86_64.target
    doc := Spec.MlKem1024.compressEncodeApi.doc
    code := Impl.MlKem1024.X86_64.compressEncode1024
    contract := Spec.MlKem1024.compressEncodeContract X86_64.abi
    verified := Proof.MlKem1024.X86_64.compressEncode1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.decodeDecompressApi with
    target := X86_64.target
    doc := Spec.MlKem1024.decodeDecompressApi.doc
    code := Impl.MlKem1024.X86_64.decodeDecompress1024
    contract := Spec.MlKem1024.decodeDecompressContract X86_64.abi
    verified := Proof.MlKem1024.X86_64.decodeDecompress1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.checkEkApi with
    target := X86_64.target
    doc := Spec.MlKem1024.checkEkApi.doc
    code := Impl.MlKem1024.X86_64.checkEk1024
    contract := Spec.MlKem1024.checkEkContract X86_64.abi
    verified := Proof.MlKem1024.X86_64.checkEk1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlKem1024.X86_64
