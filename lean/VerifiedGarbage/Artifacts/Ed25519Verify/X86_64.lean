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
