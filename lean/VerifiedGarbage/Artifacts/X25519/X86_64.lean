module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Ifma
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Adx
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit

/-! # X25519 (RFC 7748) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.X25519.X86_64

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact X86_64.target {
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are four 64-bit words, multiplied with `mul` \
      (squares computing each cross product once) and reduced with `2^256 = 38` (mod p); the \
      inversion is a call of `vg_gf25519_r64_invert`."]
    code := Impl.X25519.X86_64.x25519
    stack := 8
    verified := Proof.X25519.X86_64.x25519_verified },
  Spec.X25519.x25519Api.artifact X86_64.target {
    suffix := "_adx"
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are four 64-bit words, multiplied and squared with \
      BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once) and reduced with \
      `2^256 = 38` (mod p); the inversion is a call of `vg_gf25519_r64_invert`. The same code as \
      `vg_x25519` but for the field multiplications."]
    code := Impl.X25519.X86_64.x25519Adx
    stack := 8
    verified := Proof.X25519.X86_64.x25519Adx_verified
    features := ["bmi2", "adx"] },
  Spec.X25519.x25519Api.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. The ladder runs the four field multiplications of each of its \
      three stages at once, one to each 64-bit lane of `ymm` registers, with AVX512_IFMA's \
      `vpmadd52luq` and `vpmadd52huq`: field elements are five 51-bit limbs, reduced with \
      `2^255 = 19` (mod p), each product's first operand in `ymm16`–`ymm20` (EVEX-encoded, \
      with AVX512F and AVX512VL). It sets MXCSR to `0x1FBF` for the ladder (Intel's mitigation of \
      MXCSR-configuration-dependent timing) and restores the caller's. The inversion is a \
      call of `vg_gf25519_r64_invert`."]
    code := Impl.X25519.X86_64.x25519Ifma
    stack := 8
    verified := Proof.X25519.X86_64.x25519Ifma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"] },
  Spec.X25519.x25519BaseApi.artifact X86_64.target {
    notes := ["Ed25519's fixed-base comb, from its \
      tables in the static `VG_ED25519_COMB`, with the scalar clamped as RFC 7748 specifies and \
      the point mapped to `(Z + Y) / (Z - Y)`, inverting with a call of `vg_gf25519_r64_invert`. \
      The table selection is constant time; the callee-saved registers are saved in `scratch`. \
      The comb's five doublings and 51 additions are calls of `vg_ed25519_r64_double_ext` and \
      `vg_ed25519_r64_add_affine_ext`."]
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.X25519.X86_64.Base.x25519Base Impl.X25519.X86_64.baseline
    stack := 8
    verified := Proof.X25519.X86_64.Base.x25519Base_verified },
  Spec.X25519.x25519BaseApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["The same fixed-base comb as \
      `vg_x25519_base`, with BMI2 and ADX field arithmetic, its table entries selected 32 bytes \
      at a time with AVX2, and its doublings and additions calls of \
      `vg_ed25519_r64_double_ext_adx` and `vg_ed25519_r64_add_affine_ext_adx`."]
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.X25519.X86_64.Base.x25519BaseAdx
    stack := 8
    verified := Proof.X25519.X86_64.Base.x25519BaseAdx_verified
    features := ["avx", "avx2", "bmi2", "adx"] },
  Spec.X25519.x25519BaseApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["The fixed-base comb of \
      `vg_x25519_base_adx` with two accumulated points, one in each half of `zmm` registers, \
      as `vg_ed25519_scalar_base_ifma`'s: one sums the entries of the odd digits and the other \
      those of the even digits, two tables' entries at once with AVX512_IFMA's `vpmadd52luq` \
      and `vpmadd52huq`, and the first, doubled five times, is added to the second at the end. \
      The comb runs with MXCSR `0x1FBF` (Intel's MCDT prologue and epilogue), saved in \
      `scratch` and restored."]
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.X25519.X86_64.Base.x25519BaseIfma
    stack := 8
    verified := Proof.X25519.X86_64.Base.x25519BaseIfma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"] }]

end VG.Artifacts.X25519.X86_64
