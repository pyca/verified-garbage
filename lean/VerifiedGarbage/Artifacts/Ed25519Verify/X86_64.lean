module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyCT
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! Complete strict Ed25519 equation verification with a caller-supplied SHA-512 challenge. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.X86_64

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact X86_64.target {
    notes := ["Uses baseline integer instructions. \
      Checks canonical point encodings and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. No additional subgroup or small-order policy is imposed. \
      Computes [k]A - [S]B with one chain of doublings, recoding both scalars into signed odd \
      digits at least w positions apart (w = 5 for k, from a table of ±[1]A to ±[15]A; w = 8 \
      for S, from the static VG_ED25519_VERIFY_BASE of ∓[1]B to ∓[127]B), both cached for \
      addition as [Y - X, Y + X, 2dT, 2Z], skipping the leading zero bytes of k above its low \
      32 and the leading zero digits, computing T only in a doubling or addition that an \
      addition follows, and compares it with -R projectively. The additions, and the doubling \
      of the table, are calls of vg_ed25519_r64_add_cached_ext and _proj and \
      vg_ed25519_r64_double_ext, whose return address takes 8 bytes of stack; the chain's \
      doublings are inline, and so are the additions of the static's entries below the \
      highest position, which take one product fewer since their Z is 1."]
    code := Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.baseline
      (Impl.Ed25519.X86_64.windows Impl.X25519.X86_64.baseline)
    consts := Impl.Ed25519.X86_64.baseOddConsts
    stack := 8
    verified := Proof.Ed25519.X86_64.verify_verified8 (win := Impl.Ed25519.X86_64.windowsWith
      Impl.X25519.X86_64.baseline (Impl.Ed25519.X86_64.Point64.bodies Impl.X25519.X86_64.baseline)) rfl
      Proof.Ed25519.X86_64.VerifyCode.baseline_inlineOk Proof.Ed25519.X86_64.VerifyCode.baseline_mxI
    spSafe := Proof.Ed25519.X86_64.VerifyCode.baseline_spSafe },
  Spec.Ed25519.verifyEquationApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["The code of \
      `vg_ed25519_verify_equation` but for the field multiplications and squarings, which use \
      BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once), as `vg_x25519_adx` \
      does. Checks canonical point encodings and S < L, then evaluates the uncofactored \
      equation using all 512 challenge bits, with one chain of doublings and signed odd digits \
      of k (w = 5) and of S (w = 8), skipping the leading zero bytes of k above its low 32 \
      and the leading zero digits. The additions, and the doubling of the table, are calls of \
      the `_adx` point functions, whose return address takes 8 bytes of stack; the chain's \
      doublings are inline, and so are the additions of the static's entries below the \
      highest position, which take one product fewer since their Z is 1."]
    code := Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
      (Impl.Ed25519.X86_64.windows Impl.X25519.X86_64.adx)
    consts := Impl.Ed25519.X86_64.baseOddConsts
    stack := 8
    verified := Proof.Ed25519.X86_64.verify_verified8 (win := Impl.Ed25519.X86_64.windowsWith
      Impl.X25519.X86_64.adx (Impl.Ed25519.X86_64.Point64.bodies Impl.X25519.X86_64.adx)) rfl
      Proof.Ed25519.X86_64.VerifyCode.adx_inlineOk Proof.Ed25519.X86_64.VerifyCode.adx_mxI
    features := ["bmi2", "adx"]
    spSafe := Proof.Ed25519.X86_64.VerifyCode.adx_spSafe },
  Spec.Ed25519.verifyEquationApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["The code of \
      `vg_ed25519_verify_equation_adx` but for its windows, which hold the point's coordinates \
      `X, Y, Z, T` in the four lanes of `ymm` registers throughout, as five 51-bit limbs each: \
      each doubling, and each addition of a digit's cached table entry (loaded and split into \
      limbs), is two four-lane multiplications (AVX512_IFMA's `vpmadd52luq` and \
      `vpmadd52huq` on `ymm` registers, with AVX512VL), as in `vg_ed25519_scalar_base_ifma`'s \
      comb. The windows run between Intel's MXCSR prologue and epilogue, which save MXCSR \
      through bytes 1600 to 1608 of `scratch`. The table of A's multiples is built with calls of \
      vg_ed25519_r64_double_ext_adx and vg_ed25519_r64_add_cached_ext_adx, whose return address \
      takes 8 bytes of stack."]
    code := Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
      Impl.Ed25519.X86_64.Ifma.windows
    consts := Impl.Ed25519.X86_64.baseOddConsts
    stack := 8
    verified := Proof.Ed25519.X86_64.verify_verified8 (win := Impl.Ed25519.X86_64.Ifma.windows)
      Proof.Ed25519.X86_64.VerifyCode.ifma_windows_inline
      Proof.Ed25519.X86_64.VerifyCode.ifma_inlineOk Proof.Ed25519.X86_64.VerifyCode.ifma_mxI
    features := ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
    spSafe := Proof.Ed25519.X86_64.VerifyCode.ifma_spSafe }]

end VG.Artifacts.Ed25519Verify.X86_64
