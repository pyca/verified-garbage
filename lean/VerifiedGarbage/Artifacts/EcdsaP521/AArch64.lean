module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.P521.Comb7
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
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
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64
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
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
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
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P521
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # ECDSA over P-521 (FIPS 186-5) on AArch64 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-521 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP521.AArch64.Rfc6979

open VG.Proof.P521.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p521 p521T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P521_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p521 hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law)) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs
      stack := stackT
      verified := p521T_verified hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law) vs hv }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.AArch64.variants

end VG.Artifacts.EcdsaP521.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Verify.AArch64.verifyP521
    stack := 80
    verified := Proof.Ecdsa.Verify.AArch64.P521.verifyHash_verified hasLaw.law hasLaw.prime hasLaw.inv (Proof.P521.combOk7 hasLaw.law) }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP521.AArch64
