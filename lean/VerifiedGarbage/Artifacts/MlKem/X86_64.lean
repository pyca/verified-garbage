import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-KEM (FIPS 203) on x86-64: the polynomial primitives -/

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact := [
  { Spec.MlKem.encryptMulApi with
    target := X86_64.target
    doc := Spec.MlKem.encryptMulApi.doc
      (notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.encryptMul .sse 3
    contract := Spec.MlKem.encryptMulContract 3 X86_64.abi
    verified := Proof.MlKem.X86_64.encMulSse3_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.encryptMulApi with
    name := Spec.MlKem.encryptMulApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.encryptMulApi.doc
      (notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2`, `vg_mlkem_add_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 \
        registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.encryptMul .avx2 3
    contract := Spec.MlKem.encryptMulContract 3 X86_64.abi
    verified := Proof.MlKem.X86_64.encMulAvx3_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.decryptMulApi with
    target := X86_64.target
    doc := Spec.MlKem.decryptMulApi.doc
      (notes := ["The function computes with the code of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, \
        `vg_mlkem_add` and `vg_mlkem_inv_ntt` inlined, on SSE2 registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.decryptMul .sse 3
    contract := Spec.MlKem.decryptMulContract 3 X86_64.abi
    verified := Proof.MlKem.X86_64.decMulSse3_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.decryptMulApi with
    name := Spec.MlKem.decryptMulApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.decryptMulApi.doc
      (notes := ["The function computes with the code of `vg_mlkem_ntt_avx2`, \
        `vg_mlkem_multiply_ntts_avx2`, `vg_mlkem_add_avx2` and `vg_mlkem_inv_ntt_avx2` inlined, on AVX2 \
        registers. It sets MXCSR to `0x1FBF` once \
        around all its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and \
        loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.decryptMul .avx2 3
    contract := Spec.MlKem.decryptMulContract 3 X86_64.abi
    verified := Proof.MlKem.X86_64.decMulAvx3_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.nttApi with
    target := X86_64.target
    doc := Spec.MlKem.nttApi.doc
      (notes := ["The function computes on eight coefficients at a time in SSE2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.ntt
    contract := Spec.MlKem.nttContract X86_64.abi
    verified := Proof.MlKem.X86_64.ntt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttInvApi with
    target := X86_64.target
    doc := Spec.MlKem.nttInvApi.doc
      (notes := ["The function computes on eight coefficients at a time in SSE2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.nttInv
    contract := Spec.MlKem.nttInvContract X86_64.abi
    verified := Proof.MlKem.X86_64.nttInv_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttApi with
    name := Spec.MlKem.nttApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.nttApi.doc
      (notes := ["The function computes on sixteen coefficients at a time in AVX2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.nttAvx2
    contract := Spec.MlKem.nttContract X86_64.abi
    verified := Proof.MlKem.X86_64.nttY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"]
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.addApi with
    target := X86_64.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.X86_64.add
    contract := Spec.MlKem.addContract X86_64.abi
    verified := Proof.MlKem.X86_64.add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.subApi with
    target := X86_64.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.X86_64.sub
    contract := Spec.MlKem.subContract X86_64.abi
    verified := Proof.MlKem.X86_64.sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.addApi with
    name := Spec.MlKem.addApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.addApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers. It has no \
        multiplications."])
    code := Impl.MlKem.X86_64.addAvx2
    contract := Spec.MlKem.addContract X86_64.abi
    verified := Proof.MlKem.X86_64.addY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.subApi with
    name := Spec.MlKem.subApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.subApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers. It has no \
        multiplications."])
    code := Impl.MlKem.X86_64.subAvx2
    contract := Spec.MlKem.subContract X86_64.abi
    verified := Proof.MlKem.X86_64.subY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.mulApi with
    target := X86_64.target
    doc := Spec.MlKem.mulApi.doc
      (notes := ["The function computes on eight pairs of coefficients at a time in SSE2 registers. It sets \
        MXCSR to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.multiplyNTTs
    contract := Spec.MlKem.mulContract X86_64.abi
    verified := Proof.MlKem.X86_64.mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.mulApi with
    name := Spec.MlKem.mulApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.mulApi.doc
      (notes := ["The function computes on sixteen pairs of coefficients at a time in AVX2 registers. It sets \
        MXCSR to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.multiplyNTTsAvx2
    contract := Spec.MlKem.mulContract X86_64.abi
    verified := Proof.MlKem.X86_64.mulY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.sampleNTTApi with
    target := X86_64.target
    doc := Spec.MlKem.sampleNTTApi.doc
    code := Impl.MlKem.X86_64.sampleNTT
    contract := Spec.MlKem.sampleNTTContract X86_64.abi 16
    stack := 16
    verified := Proof.MlKem.X86_64.sample_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.encode12Api with
    target := X86_64.target
    doc := Spec.MlKem.encode12Api.doc
    code := Impl.MlKem.X86_64.encode12
    contract := Spec.MlKem.encode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.encode12_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.decode12Api with
    target := X86_64.target
    doc := Spec.MlKem.decode12Api.doc
    code := Impl.MlKem.X86_64.decode12
    contract := Spec.MlKem.decode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.decode12_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.decode12Api with
    name := Spec.MlKem.decode12Api.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.decode12Api.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers, from 12 bytes \
        loaded 16 at a time (the last 12 from 4 bytes before them, so that it reads only the 384 bytes of \
        `*b`). It has no multiplications."])
    code := Impl.MlKem.X86_64.decode12Avx2
    contract := Spec.MlKem.decode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.decode12Y_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.cbd2Api with
    target := X86_64.target
    doc := Spec.MlKem.cbd2Api.doc
    code := Impl.MlKem.X86_64.cbd2
    contract := Spec.MlKem.cbd2Contract X86_64.abi
    verified := Proof.MlKem.X86_64.cbd2_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.compressEncodeApi with
    target := X86_64.target
    doc := Spec.MlKem.compressEncodeApi.doc
    code := Impl.MlKem.X86_64.compressEncode
    contract := Spec.MlKem.compressEncodeContract X86_64.abi
    verified := Proof.MlKem.X86_64.compressEncode_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.decodeDecompressApi with
    target := X86_64.target
    doc := Spec.MlKem.decodeDecompressApi.doc
    code := Impl.MlKem.X86_64.decodeDecompress
    contract := Spec.MlKem.decodeDecompressContract X86_64.abi
    verified := Proof.MlKem.X86_64.decodeDecompress_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.checkEkApi with
    target := X86_64.target
    doc := Spec.MlKem.checkEkApi.doc
    code := Impl.MlKem.X86_64.checkEk
    contract := Spec.MlKem.checkEkContract X86_64.abi
    verified := Proof.MlKem.X86_64.checkEk_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.sampleNTT4Api with
    target := X86_64.target
    doc := Spec.MlKem.sampleNTT4Api.doc
      (notes := ["The function calls `vg_mlkem_sample_ntt` on each seed, with 24 bytes of stack below its \
        return address."])
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4
    contract := Spec.MlKem.sampleNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_scalar_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.sampleNTT4Api with
    name := Spec.MlKem.sampleNTT4Api.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.sampleNTT4Api.doc
      (notes := ["The function absorbs the four seeds and squeezes the four instances of SHAKE128 at once, \
        each 64-bit lane of the Keccak states in a 256-bit AVX2 register holding that lane of all four; \
        it then samples from the output of each in turn, eight candidates at a time in AVX2 registers \
        (keeping those less than `q` with `vpermd`, by a table in `*scratch` indexed by their mask), \
        and finishes any that needs more than the 504 bytes it squeezed with `vg_mlkem_sample_ntt`, \
        with 24 bytes of stack below its return address."])
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2
    contract := Spec.MlKem.sampleNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlKem.sampleNTT4Api with
    name := Spec.MlKem.sampleNTT4Api.name ++ "_avx512"
    target := X86_64.target
    doc := Spec.MlKem.sampleNTT4Api.doc
      (notes := ["The function absorbs the four seeds and squeezes the four instances of SHAKE128 at once, \
        each 64-bit lane of the Keccak states in a 256-bit AVX2 register holding that lane of all four; \
        it then samples from the output of each in turn, eight candidates at a time in AVX2 registers \
        (keeping those less than `q` with `vpermd`, by a table in `*scratch` indexed by their mask), \
        and finishes any that needs more than the 504 bytes it squeezed with `vg_mlkem_sample_ntt`, \
        using AVX-512VL quadword rotates in Keccak, with 24 bytes of stack below its return address."])
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 true
    contract := Spec.MlKem.sampleNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2", "avx512f", "avx512vl"] }]

end VG.Artifacts.MlKem.X86_64
