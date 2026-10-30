module
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomery
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on x86-64: the arithmetic of polynomials -/

@[expose] public section

namespace VG.Artifacts.MlDsaArith.X86_64

def artifacts : List Artifact := [
  Spec.MlDsa.nttApi.artifact X86_64.target {
    notes := ["The function computes on four coefficients at a time in SSE2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."]
    code := Impl.MlDsa.X86_64.Arith.ntt
    verified := Proof.MlDsa.X86_64.Arith.ntt_verified },
  Spec.MlDsa.nttInvApi.artifact X86_64.target {
    notes := ["The function computes on four coefficients at a time in SSE2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."]
    code := Impl.MlDsa.X86_64.Arith.nttInv
    verified := Proof.MlDsa.X86_64.Arith.nttInv_verified },
  Spec.MlDsa.mulApi.artifact X86_64.target {
    notes := ["The function computes on four coefficients at a time in SSE2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."]
    code := Impl.MlDsa.X86_64.Arith.mul
    verified := Proof.MlDsa.X86_64.Arith.mul_verified },
  Spec.MlDsa.mulAddApi.artifact X86_64.target {
    notes := ["The function computes on four coefficients at a time in SSE2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."]
    code := Impl.MlDsa.X86_64.Arith.mulAdd
    verified := Proof.MlDsa.X86_64.Arith.mulAdd_verified },
  Spec.MlDsa.addApi.artifact X86_64.target {
    notes := ["The function computes on four coefficients at a time in SSE2 registers."]
    code := Impl.MlDsa.X86_64.Arith.add
    verified := Proof.MlDsa.X86_64.Arith.add_verified },
  Spec.MlDsa.subApi.artifact X86_64.target {
    notes := ["The function computes on four coefficients at a time in SSE2 registers."]
    code := Impl.MlDsa.X86_64.Arith.sub
    verified := Proof.MlDsa.X86_64.Arith.sub_verified },
  Spec.MlDsa.nttApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."]
    code := Impl.MlDsa.X86_64.Arith.lazyNtt
    verified := Proof.MlDsa.X86_64.Arith.Lazy.verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.montgomeryNttInvApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. Its butterflies do not reduce: a coefficient's bound \
        doubles each layer, from `q` to `256 q`, and the final multiplication by `R/256` reduces each. It \
        sets MXCSR to `0x1FBF` around its multiplications (Intel's mitigation of \
        MXCSR-configuration-dependent timing) and loads the caller's MXCSR back before returning."]
    code := Impl.MlDsa.X86_64.Arith.montNttInvAvx2
    verified := Proof.MlDsa.X86_64.Arith.MontgomeryInv.verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.montgomeryMulApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."]
    code := Impl.MlDsa.X86_64.Arith.montMulAvx2
    verified := Proof.MlDsa.X86_64.Arith.montMulY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.montgomeryMulAddApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."]
    code := Impl.MlDsa.X86_64.Arith.montMulAddAvx2
    verified := Proof.MlDsa.X86_64.Arith.montMulAddY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.addApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers."]
    code := Impl.MlDsa.X86_64.Arith.addAvx2
    verified := Proof.MlDsa.X86_64.Arith.addY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.subApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 registers."]
    code := Impl.MlDsa.X86_64.Arith.subAvx2
    verified := Proof.MlDsa.X86_64.Arith.subY_verified
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlDsaArith.X86_64
