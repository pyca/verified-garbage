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
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
public import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
public import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.Decode
public import VerifiedGarbage.Proof.Ed25519.Group.Decode
public import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Proof.Ed25519.ScalarBytes
public import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
public import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
public import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
public import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
public import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
public import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
public import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
public import VerifiedGarbage.Proof.Ed25519.X86_64.Points
public import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
public import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
public import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
public import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.X25519.X86_64.AddSub
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.X25519.X86_64.Bits
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
public import VerifiedGarbage.Proof.X25519.X86_64.Finish
public import VerifiedGarbage.Proof.X25519.X86_64.Freeze
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step
public import VerifiedGarbage.Proof.X25519.X86_64.Inv
public import VerifiedGarbage.Proof.X25519.X86_64.Invert
public import VerifiedGarbage.Proof.X25519.X86_64.Sqr
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Sqr

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
