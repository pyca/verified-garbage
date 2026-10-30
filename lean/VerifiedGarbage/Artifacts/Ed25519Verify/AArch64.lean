module

public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ed25519.AArch64.Point64
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
public import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter
public import VerifiedGarbage.Proof.Ed25519.AArch64.Points
public import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
public import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarWord
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
public import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.Decode
public import VerifiedGarbage.Proof.Ed25519.Field64
public import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Mont.AArch64.Blocks
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
public import VerifiedGarbage.Proof.Mont.AArch64.Csub
public import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Impl.Ed25519.AArch64.Point64
import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarWord
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.Field64
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Rounds

/-! Complete strict Ed25519 equation verification with a caller-supplied SHA-512 challenge. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact AArch64.target {
    consts := Impl.Ed25519.AArch64.bConsts
    code := Impl.Ed25519.AArch64.verifyEquation
    verified := Proof.Ed25519.AArch64.verify_verified }]

end VG.Artifacts.Ed25519Verify.AArch64
