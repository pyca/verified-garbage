module

public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12Avx2
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.MulYV
public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
public import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Scalar
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
public import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-KEM (FIPS 203) on x86-64: the polynomial primitives -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact := [
  Spec.MlKem.encryptMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.encryptMul .sse 3
    verified := Proof.MlKem.X86_64.encMulSse3_verified },
  Spec.MlKem.encryptMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 registers: the `NTT`s \
        first, as 16-bit words in the order the products read them, then each output's products summed in \
        16-bit words and its `NTT⁻¹`. It sets MXCSR to `0x1FBF` once around all its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."]
    code := Impl.MlKem.X86_64.encryptMulY 3
    verified := Proof.MlKem.X86_64.encMulY3_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.decryptMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.decryptMul .sse 3
    verified := Proof.MlKem.X86_64.decMulSse3_verified },
  Spec.MlKem.decryptMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 registers: the `NTT`s \
        first, as 16-bit words in the order the products read them, then each output's products summed in \
        16-bit words and its `NTT⁻¹`. It sets MXCSR to `0x1FBF` once around all its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."]
    code := Impl.MlKem.X86_64.decryptMulY 3
    verified := Proof.MlKem.X86_64.decMulY3_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.keygenMulApi.artifact X86_64.target {
    notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts` and \
        `vg_mlkem_add` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once around all its \
        multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the \
        caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.keygenMul .sse 3
    verified := Proof.MlKem.X86_64.kgMulSse3_verified },
  Spec.MlKem.keygenMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes with the code of `vg_mlkem_ntt_avx2` and \
        `vg_mlkem_multiply_ntts_avx2` inlined, on AVX2 registers, summing each row's products in 16-bit \
        words. It sets MXCSR to `0x1FBF` once around all its multiplications (Intel's mitigation of \
        MXCSR-configuration-dependent timing) and loads the caller's MXCSR back before returning."]
    code := Impl.MlKem.X86_64.keygenMul .avx2 3
    verified := Proof.MlKem.X86_64.kgMulAvx3_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.addApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.add
    verified := Proof.MlKem.X86_64.add_verified },
  Spec.MlKem.subApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.sub
    verified := Proof.MlKem.X86_64.sub_verified },
  Spec.MlKem.addApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers. It has no \
        multiplications."]
    code := Impl.MlKem.X86_64.addAvx2
    verified := Proof.MlKem.X86_64.addY_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.subApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers. It has no \
        multiplications."]
    code := Impl.MlKem.X86_64.subAvx2
    verified := Proof.MlKem.X86_64.subY_verified
    features := ["avx", "avx2"] },
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
  Spec.MlKem.decode12Api.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers, from 12 bytes \
        loaded 16 at a time (the last 12 from 4 bytes before them, so that it reads only the 384 bytes of \
        `*b`). It has no multiplications."]
    code := Impl.MlKem.X86_64.decode12Avx2
    verified := Proof.MlKem.X86_64.decode12Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.encode12Api.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on 32 coefficients at a time in AVX2 registers: it packs them into \
        words, forms each pair's 24-bit value with shifts and an addition, gathers the bytes with `vpshufb` \
        and `vpermd`, and stores the 48 bytes as 32 and 16, so that it writes only the 384 bytes of `*out`. \
        It has no multiplications."]
    code := Impl.MlKem.X86_64.encode12Avx2
    verified := Proof.MlKem.X86_64.encode12Y_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.cbd2Api.artifact X86_64.target {
    code := Impl.MlKem.X86_64.cbd2
    verified := Proof.MlKem.X86_64.cbd2_verified },
  Spec.MlKem.compressEncodeApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.compressEncode
    verified := Proof.MlKem.X86_64.compressEncode_verified },
  Spec.MlKem.decodeDecompressApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.decodeDecompress
    verified := Proof.MlKem.X86_64.decodeDecompress_verified },
  Spec.MlKem.compressEncodeApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["For the widths 10 and 4, the function compresses eight coefficients at a time in AVX2 \
        registers, multiplying by sums of shifts, and packs them with `vpsllvd`, `vpsllvq` and `vpshufb`; \
        the width 1 runs the baseline loop. It writes only the `len` bytes of `*out`."]
    code := Impl.MlKem.X86_64.compressEncodeAvx2
    verified := Proof.MlKem.X86_64.compressEncodeY_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.decodeDecompressApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["For the widths 10 and 4, the function decompresses eight values at a time in AVX2 \
        registers, extracted with `vpshufb` and `vpsrlvd` from 16 bytes loaded into both lanes, multiplying \
        by sums of shifts; the width 1 runs the baseline loop. It reads only the `len` bytes of `*b`."]
    code := Impl.MlKem.X86_64.decodeDecompressAvx2
    verified := Proof.MlKem.X86_64.decodeDecompressY_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.checkEkApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.checkEk
    verified := Proof.MlKem.X86_64.checkEk_verified },
  Spec.MlKem.sampleNTT4Api.artifact X86_64.target {
    notes := ["The function calls `vg_mlkem_sample_ntt` on each seed, with 24 bytes of stack below its \
        return address."]
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_scalar_verified },
  Spec.MlKem.sampleNTT4Api.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function absorbs the four seeds and squeezes the four instances of SHAKE128 at once, \
        each 64-bit lane of the Keccak states in a 256-bit AVX2 register holding that lane of all four; \
        it then samples from the output of each in turn, eight candidates at a time in AVX2 registers \
        (keeping those less than `q` with `vpermd`, by a table in `*scratch` indexed by their mask). \
        Only if one needs more than the 504 bytes it squeezed of each does it squeeze two more blocks \
        of all four from the states it kept, and continues each from where it stopped. It calls \
        nothing, but is declared with the 24 bytes of stack below its return address of \
        `vg_mlkem_sample_ntt4`, whose contract it shares."]
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.sampleNTT4Api.artifact X86_64.target {
    suffix := "_avx512"
    notes := ["The function absorbs the four seeds and squeezes the four instances of SHAKE128 at once, \
        each 64-bit lane of the Keccak states in a 256-bit AVX2 register holding that lane of all four; \
        it then samples from the output of each in turn, eight candidates at a time in AVX2 registers \
        (keeping those less than `q` with `vpermd`, by a table in `*scratch` indexed by their mask). \
        Only if one needs more than the 504 bytes it squeezed of each does it squeeze two more blocks \
        of all four from the states it kept, and continues each from where it stopped. It uses \
        AVX-512VL quadword rotates in Keccak. It calls nothing, but is declared with the 24 bytes of \
        stack below its return address of `vg_mlkem_sample_ntt4`, whose contract it shares."]
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 true
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_verified
    features := ["avx", "avx2", "avx512f", "avx512vl"] }]

end VG.Artifacts.MlKem.X86_64
