module
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic

public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic -- shake: keep (exposed backend proof fields reference these lemmas)
public import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
public import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
public import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
public import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
public import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
public import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
public import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
public import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBEArgs
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckBounds
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCalc
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckFinish
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckMath
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckRead
public import VerifiedGarbage.Proof.Bignum.Arm.MontBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
public import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
public import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
public import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
public import VerifiedGarbage.Proof.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
public import VerifiedGarbage.Proof.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.RowBody
public import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RowFull
public import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
public import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
public import VerifiedGarbage.Proof.Bignum.Arm.RowStep
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
public import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
public import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
public import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
public import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.Shift
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
public import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
public import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
public import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
public import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
public import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.Sub
public import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.SubBody
public import VerifiedGarbage.Proof.Bignum.Arm.SubRow
public import VerifiedGarbage.Proof.Bignum.Arm.SubStep
public import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGe
public import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGeCT
public import VerifiedGarbage.Proof.Bignum.Arm.WideMath
public import VerifiedGarbage.Proof.Bignum.Arm.WideValue
public import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MillerRabin.Arm.Body
public import VerifiedGarbage.Proof.MillerRabin.Arm.Mont
public import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
public import VerifiedGarbage.Proof.MillerRabin.Arm.Run
public import VerifiedGarbage.Proof.Rsa.Arm.AddMod
public import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
public import VerifiedGarbage.Proof.Rsa.Arm.CvFin
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
public import VerifiedGarbage.Proof.Rsa.Arm.DivArgs
public import VerifiedGarbage.Proof.Rsa.Arm.DivArgsCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivBit
public import VerifiedGarbage.Proof.Rsa.Arm.DivBitCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivInit
public import VerifiedGarbage.Proof.Rsa.Arm.DivInitCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivLoop
public import VerifiedGarbage.Proof.Rsa.Arm.DivReduceCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivShift
public import VerifiedGarbage.Proof.Rsa.Arm.DivShiftArray
public import VerifiedGarbage.Proof.Rsa.Arm.DivShiftCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivStep
public import VerifiedGarbage.Proof.Rsa.Arm.DivStepCT
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Rsa.Arm.InvParts
public import VerifiedGarbage.Proof.Rsa.Arm.KcOps
public import VerifiedGarbage.Proof.Rsa.Arm.KcStart
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
public import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
public import VerifiedGarbage.Proof.Rsa.Arm.RvOps
public import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
public import VerifiedGarbage.Proof.Rsa.Arm.RvViews
public import VerifiedGarbage.Proof.Rsa.Arm.ShiftRight
public import VerifiedGarbage.Proof.Rsa.KeyBits32
public import VerifiedGarbage.Proof.Rsa.KeyViews
public import VerifiedGarbage.Proof.Rsa.MulModArithmetic
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckBounds
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCalc
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckFinish
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckMath
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckRead
import VerifiedGarbage.Proof.Bignum.Arm.MontBody
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
import VerifiedGarbage.Proof.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowBody
import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGe
import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGeCT
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MillerRabin.Arm.Body
import VerifiedGarbage.Proof.MillerRabin.Arm.Mont
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.MillerRabin.Arm.Run
import VerifiedGarbage.Proof.Rsa.Arm.AddMod
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.CvFin
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
import VerifiedGarbage.Proof.Rsa.Arm.DivArgs
import VerifiedGarbage.Proof.Rsa.Arm.DivArgsCT
import VerifiedGarbage.Proof.Rsa.Arm.DivBit
import VerifiedGarbage.Proof.Rsa.Arm.DivBitCT
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.DivInit
import VerifiedGarbage.Proof.Rsa.Arm.DivInitCT
import VerifiedGarbage.Proof.Rsa.Arm.DivLoop
import VerifiedGarbage.Proof.Rsa.Arm.DivReduceCT
import VerifiedGarbage.Proof.Rsa.Arm.DivShift
import VerifiedGarbage.Proof.Rsa.Arm.DivShiftArray
import VerifiedGarbage.Proof.Rsa.Arm.DivShiftCT
import VerifiedGarbage.Proof.Rsa.Arm.DivStep
import VerifiedGarbage.Proof.Rsa.Arm.DivStepCT
import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KcOps
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvViews
import VerifiedGarbage.Proof.Rsa.Arm.ShiftRight
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Rsa.KeyViews
import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.MrMont

/-!
# The shared round on ARMv7 with `umaal`: the variant's code and proofs

The variant `VG.Variants.MillerRabin.Arm.Umaal.variant`
(`Variants/MillerRabin/Arm/Umaal.lean`): the same pipelined fused Montgomery kernel as the shared Montgomery backend
handles products and squares. The generic round proof covers that kernel;
`umaalArithmetic_verified` transfers any remaining row substitutions.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.Arm.Umaal

open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm VG.Proof.MillerRabin.Arm

theorem round_verified : Verified target (umaalArithmetic (Impl.MillerRabin.Arm.code true)) roundContract :=
  umaalArithmetic_verified (round_verified_lite true)

def variant : RoundImpl where
  code := umaalArithmetic (Impl.MillerRabin.Arm.code true)
  verified := round_verified
  stack := Nat.le_trans (armStack_umaalArithmetic _) (by decide +kernel)
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Variants.MillerRabin.Arm.Umaal
