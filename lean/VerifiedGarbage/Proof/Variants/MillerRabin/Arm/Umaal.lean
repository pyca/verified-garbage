module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic -- shake: keep (exposed backend proof fields reference these lemmas)
public import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
public import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
public import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
public import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
public import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
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
public import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
public import VerifiedGarbage.Proof.Bignum.Arm.MontState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
public import VerifiedGarbage.Proof.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.RowFull
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
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
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
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
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
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
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Views
public import VerifiedGarbage.Proof.Rsa.Arm.ShiftRight
public import VerifiedGarbage.Proof.Rsa.KeyBits32
public import VerifiedGarbage.Proof.Rsa.KeyViews
public import VerifiedGarbage.Proof.Rsa.MulModArithmetic
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.RsaKeyGen.MrMont
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Framework.Lit

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
  icallFree := by lit_decide
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Variants.MillerRabin.Arm.Umaal
