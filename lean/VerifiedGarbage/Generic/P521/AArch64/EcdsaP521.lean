module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
public import VerifiedGarbage.Impl.P256.VerifyRegisters
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointAbi
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointBoundaryTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointDigitsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixed
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedPoint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSignTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLoopTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPointsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrepTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTopTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindow
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTimingStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
public import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.CoZTable
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointBoundaryTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointDigitsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedPoint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSignTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLoopTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTopTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindow
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-! # ECDSA over P-521 (FIPS 186-5) on AArch64 -/

@[expose] public section

namespace VG.Generic.P521.AArch64.EcdsaP521

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.P521.verifyApi.artifact AArch64.target {
    consts := Impl.Ecdsa.AArch64.p521.combConsts
    code := Impl.Ecdsa.Verify.AArch64.verifyP521
    verified := Proof.Ecdsa.Verify.AArch64.P521.verify_verified h.law h.prime h.inv (Proof.P521.combOk7 h.law) }]

end VG.Generic.P521.AArch64.EcdsaP521
