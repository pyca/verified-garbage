module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.P256.GTable9
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.InvAllocated
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
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
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
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
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Proof.P256.AArch64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P256
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-256 (FIPS 186-5) on AArch64 -/

-- Deterministic ECDSA (RFC 6979) over P-256 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP256.AArch64.Rfc6979

open VG.Proof.P256.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.p256 hashes
    verified := (Proof.Ecdsa.Rfc6979.AArch64.p256Sign_scrubbed hasLaw.law hasLaw.inv
      (Proof.P256.combOk7 hasLaw.law)) }]

end VG.Artifacts.EcdsaP256.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.P256.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.P256Allocated.Fn.verifyHash
    verified := Proof.Ecdsa.Verify.AArch64.allocatedVerifyHash_scrubbed hasLaw.law hasLaw.prime hasLaw.inv hasLaw.invToM (Proof.P256.gtabOk9 hasLaw.law) }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP256.AArch64
