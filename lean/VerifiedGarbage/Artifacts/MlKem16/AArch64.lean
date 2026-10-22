module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.VerifiedF
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.VerifiedFI

/-! # ML-KEM (FIPS 203) on AArch64: the producers of polynomials with 16-bit coefficients -/

@[expose] public section

namespace VG.Artifacts.MlKem16.AArch64

def artifacts : List Artifact := [
  Spec.MlKem.cbd2_16Api.artifact AArch64.target {
    code := Impl.MlKem.AArch64.Cbd16.code16
    verified := Proof.MlKem.AArch64.Cbd16W.verified },
  Spec.MlKem.ntt16Api.artifact AArch64.target {
    notes := ["mlkem-native's schedule (its `mlkem_ntt_aarch64_asm`, scheduled by SLOTHY): layers \
        1–3 eight vectors at a time, layers 4–7 32 coefficients at a time, the zetas multiplied by \
        element; then each coefficient reduced to `[0, q)`. The low halves of `v8`–`v15` are kept \
        in `x7`–`x14`. No stack, and the working space is not used."]
    consts := Impl.MlKem.AArch64.Ntt16.Fast.tables
    code := Impl.MlKem.AArch64.Ntt16.Fast.fwdFast
    verified := Proof.MlKem.AArch64.NttR.fast_verified },
  Spec.MlKem.nttInv16Api.artifact AArch64.target {
    notes := ["mlkem-native's schedule (its `mlkem_intt_aarch64_asm`, scheduled by SLOTHY), after \
        the multiplication by `128⁻¹`: layers 7–4 32 coefficients at a time, layers 3–1 eight \
        vectors at a time, the zetas multiplied by element, its Barrett reductions replaced by \
        `x - SQRDMULH(x, 10) · q`; then each coefficient reduced to `[0, q)`. The low halves of \
        `v8`–`v15` are kept in `x7`–`x14`. No stack, and the working space is not used."]
    consts := Impl.MlKem.AArch64.Ntt16.FastInv.tables
    code := Impl.MlKem.AArch64.Ntt16.FastInv.invFast
    verified := Proof.MlKem.AArch64.NttR.fastInv_verified }]

end VG.Artifacts.MlKem16.AArch64
