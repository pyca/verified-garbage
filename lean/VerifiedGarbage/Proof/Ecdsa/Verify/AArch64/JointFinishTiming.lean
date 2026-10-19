module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCachedDigitTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCachedDigitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointPairedTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Inplace
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Inplace
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.P256.EcdhDouble.Field
import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
import VerifiedGarbage.Proof.P256.Linear.WeakAdd
import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointSignTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafCore
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTimingStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
meta import VerifiedGarbage.Impl.P256.EcdhJac
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.Projective
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.P256.EcdhDouble.Field
meta import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
meta import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
meta import VerifiedGarbage.Proof.P256.Linear.WeakAdd
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedSumTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafDigits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointSignTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafCore
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTimingStep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
meta import VerifiedGarbage.Proof.Weierstrass.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.JacInplace
meta import VerifiedGarbage.Spec.Weierstrass.Mul

/-! ## `JointChecks` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointMixed_checks : JointMixedChecks P256Joint.cfg.K P256Joint.cfg.K.R
    P256Joint.cfg.K.E P256Joint.cfg.K.D where
  zero := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> jac_field_ct
  copyQ := by jac_field_ct
  init := by jac_field_ct
  head := Forward.ArithmeticMixedHead.ct
  tail := Forward.ArithmeticMixedTail.ct
  double := Forward.rd_ct
  infinity := by jac_field_ct

theorem jointFixed_checks : JointFixedChecks P256Joint.cfg where
  lookup := VG.Taint.constantTime (A:=taintS [P256Joint.cfg.tsym]) (Taint.ofRegs [.x0,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)
  sign := by jac_reg_ct [.x0,.x19]
  neg := by jac_field_ct
  read := by jac_reg_ct [.x0,.x19]
  mixed := jointMixed_checks
  copy := by jac_field_ct

theorem jointGPrep_checks : FastPrepChecks P256Joint.cfg.G (p256.sl U) 7 where
  init := by jac_reg_ct [.x0]
  step := by jac_reg_ct [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x20]

theorem jointQPrep_checks : FastPrepChecks P256Joint.cfg.K (p256.sl V) 5 where
  init := by jac_reg_ct [.x0]
  step := by jac_reg_ct [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x20]

theorem cachedDigit_checks : CachedField.DigitChecks where
  entry := { lookup := by jac_reg_ct [.x0,.x2]
             sign := by jac_reg_ct [.x0,.x19]
             neg := by jac_field_ct }
  add := cachedAdd_checks
  copy := by jac_field_ct
  digit := by jac_reg_ct [.x0,.x19]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedRunTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem allocatedOps_timing (raw : RawCorrect) {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p) :
    JointOpsTiming cfg P256Allocated.ops C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) where
  double := by
    intro A j E
    dsimp only [P256Allocated.ops]
    have h := fieldWP_relCT (base:=base) (V:=jointLive cfg) (V':=jointLive cfg) (E:=E)
      Proof.P256.EcdhDouble.Certificate.ct fun _ hi =>
        WP.mono (double_field_ok hi) fun _ ⟨hk,it⟩ => ⟨it,hk.regs.sp⟩
    exact h.mono (fun _ _ h => h.1) (fun _ _ h => ⟨_,h⟩)
  peer := by
    intro A j hj E
    exact (cachedDigit_relCT raw (base:=base) (E:=E) hm hOne hj cachedDigit_checks).mono
      (fun _ _ h => ⟨h.1,h.2.1.stable,h.2.2.1.stable,h.2.2.2⟩) (fun _ _ h => h)
  generator := by
    intro A j hj E
    exact fixedDigit_relCT raw hC hm hOne hj jointFixed_checks

theorem allocatedRun_timing (raw : RawCorrect) {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : K.one<C.p) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) :
    RelCT isa (JointPair cfg C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) .infinity 256)
      (Joint.run cfg P256Allocated.ops)
      (JointPair cfg C base 8192
        (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T))
        (add (mul u P) (mul v Q)) 0) :=
  allocatedJointPair_run hC hP hQ hu hv (ops_ok raw hC ha hm hOne hP hQ)
    (allocatedOps_timing raw hm hC hOne) (by jac_reg_ct [.x19])

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `JointRunTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open P256Joint

theorem jointOps_timing {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) (hC : Law C) (hOne : cfg.K.one<C.p) :
    JointOpsTiming cfg ops C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) where
  double := by
    intro A j E
    dsimp only [ops]
    have h := Forward.Arithmetic.double_relCT (S:=cfg.K.S) (p:=cfg.K.R) Forward.Arithmetic.cases
      (base:=base) (E:=E) JointLayout.layout.lay JointLayout.layout.aligned hm (by decide)
      (by decide +kernel) (Low.small (by decide) _) (jointLive_R cfg) Forward.ArithmeticRR.ct
    exact h.mono (fun _ _ h => h.1) (fun _ _ h => ⟨_,h⟩)
  peer := by
    intro A j hj E
    exact (CachedField.digit_relCT (base:=base) (E:=E) JointLayout.layout (by decide) hm hOne hj cachedDigit_checks).mono
      (fun _ _ h => ⟨h.1,h.2.1.stable,h.2.2.1.stable,h.2.2.2⟩) (fun _ _ h => h)
  generator := by
    intro A j hj E
    exact jointFixedDigit_relCT Forward.Arithmetic.cases JointLayout.fixedLayout hC hm (by decide) hOne hj jointFixed_checks

theorem jointRun_timing {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : cfg.K.one<C.p) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) :
    RelCT isa (JointPair cfg C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) .infinity 256)
      (Joint.run cfg ops)
      (JointPair cfg C base 8192
        (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T))
        (add (mul u P) (mul v Q)) 0) := by
  exact jointPair_run hC hP hQ hu hv (jointOps_ok hm hC ha hOne hP hQ)
    (jointOps_timing hm hC hOne) (by jac_reg_ct [.x19])

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointFinishTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open P256Joint

theorem jointFinish_relCT (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q A : Point p256.C} {u v j : Nat} :
    RelCT isa (JointPair cfg p256.C base 8192
      (JointCore cfg p256.C base 8192 Q u v (JointGenerator cfg p256.C base 8192 P T)) A j)
      (Jacobian.jacFinish cfg.K) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,_,_⟩ es et
  have hm : UnitMod p256.C.p (2^(64*cfg.K.M.n)) := unitMod_pow_two hc.p_odd _
  have one : cfg.K.one<p256.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hone : toM p256.C.p (2^(64*cfg.K.M.n)) cfg.K.one=1 := toM_cmont hc.toBaseCfgOk 1
  obtain ⟨_,_,xs,ks,us,ms,ls,rs⟩ := jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl)
    hm hC one hone (by decide) cs
  obtain ⟨_,_,xt,kt,ut,mt,lt,rt⟩ := jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl)
    hm hC one hone (by decide) ct
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨jointFinish_ct _ _ _ _ _ _ trivial trivial hp.public es et,
    ks.sp.trans (hp.sp.trans kt.sp.symm),fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
  subst hr
  rw [ks.gpr _ (by decide),kt.gpr _ (by decide)]
  exact hp.left.scr.x0.trans hp.right.scr.x0.symm

end VG.Proof.Ecdsa.Verify.AArch64

end
