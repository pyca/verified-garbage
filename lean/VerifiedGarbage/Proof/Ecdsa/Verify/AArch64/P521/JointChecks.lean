module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
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
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
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
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PubNaf
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
meta import VerifiedGarbage.Impl.P256.VerifyRegisters
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
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
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
meta import VerifiedGarbage.Proof.Ecdsa.Projective
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedLayout
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CoZField
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
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
meta import VerifiedGarbage.Proof.Weierstrass.CoZTable
meta import VerifiedGarbage.Proof.Weierstrass.WinJacMath
meta import VerifiedGarbage.Spec.Weierstrass.Mul

/-! Concrete timing certificates for the joint P-521 verifier. -/
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64

theorem prep7_checks : PubNafWide.PrepChecks P521Joint.KG (p521.sl U) where
  init := by reg_ct [.x0]
  step := by reg_ct (PubNaf.prepPublic P521Joint.KG.M.n)

theorem prep5_checks : PubNaf.PrepChecks P521Joint.K (p521.sl V) :=
  P521.prep_checks

theorem before_ct : ConstantTime isa (fun _=>True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p521) :=
  LaneTaint.constantTime (Taint.ofRegs [.x0,.x1,.x2,.x3]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem tail_ct : FieldCT (VG.Impl.Ecdsa.Verify.AArch64.Cfg.tail p521) := by reg_ct [.x0]
theorem mixed_checks : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D where
  zero := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> reg_ct [.x0]
  copyQ := by reg_ct [.x0]
  init := by reg_ct [.x0]
  head := by reg_ct [.x0]
  tail := by reg_ct [.x0]
  double := by reg_ct [.x0]
  infinity := by reg_ct [.x0]
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
