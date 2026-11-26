module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Impl.AArch64Instrs
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
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
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
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
import VerifiedGarbage.Proof.P521.AArch64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P521
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-521 (FIPS 186-5) on AArch64 -/

-- Deterministic ECDSA (RFC 6979) over P-521 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP521.AArch64.Rfc6979

open VG.Proof.P521.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.p521 hashes
    verified := Proof.Ecdsa.Rfc6979.AArch64.p521Sign_scrubbed hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law) }]

end VG.Artifacts.EcdsaP521.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.P521.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP521
    verified := Proof.Ecdsa.Rfc6979.AArch64.p521Verify hasLaw.law hasLaw.prime hasLaw.inv (Proof.P521.combOk7 hasLaw.law) }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP521.AArch64
