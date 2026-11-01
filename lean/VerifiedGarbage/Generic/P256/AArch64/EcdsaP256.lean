module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P256.GTable9
public import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.BitVec
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.InvAllocated
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.Lit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.Finset.Card
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedVerified
import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
public import VerifiedGarbage.Impl.P256.EcdhJac
public import VerifiedGarbage.Proof.Divstep.Batch
public import VerifiedGarbage.Proof.Divstep.Incl
public import VerifiedGarbage.Proof.Divstep.Tc
public import VerifiedGarbage.Proof.Divstep.Word
public import VerifiedGarbage.Proof.EcKey.AArch64.Verified
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.P256.EcdhDouble.Field
public import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
public import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
public import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
public import VerifiedGarbage.Proof.P256.Linear.WeakAdd
public import VerifiedGarbage.Proof.P256.Point
public import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
public import VerifiedGarbage.Proof.P256.VerifyTable.Env
public import VerifiedGarbage.Proof.P256.VerifyTable.Store
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafDigits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombProduction
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyCheck
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
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
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
public import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.EcKey.AArch64.Verified
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.P256.EcdhDouble.Field
import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
import VerifiedGarbage.Proof.P256.Linear.WeakAdd
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
import VerifiedGarbage.Proof.P256.VerifyTable.Env
import VerifiedGarbage.Proof.P256.VerifyTable.Store
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyCheck
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-! # ECDSA over P-256 (FIPS 186-5) on AArch64 -/

@[expose] public section

namespace VG.Generic.P256.AArch64.EcdsaP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.verifyApi.artifact AArch64.target {
    consts := Impl.Ecdsa.Verify.AArch64.P256Joint.p256v.combConsts
    code := Impl.Ecdsa.Verify.AArch64.P256Allocated.verify
    verified := Proof.Ecdsa.Verify.AArch64.allocatedVerify_verified h.law h.prime h.inv h.invToM (Proof.P256.gtabOk9 h.law) }]

end VG.Generic.P256.AArch64.EcdsaP256
