module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Impl.Ecdh.P224.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.P224.AArch64.Law
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-224 (FIPS 186-5) on AArch64 -/

-- Deterministic ECDSA (RFC 6979) over P-224 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP224.AArch64.Rfc6979

open VG.Proof.P224.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.p224 hashes
    verified := Proof.Ecdsa.Rfc6979.AArch64.p224Sign_scrubbed hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) }]

end VG.Artifacts.EcdsaP224.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.P224.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP224
    verified := Proof.Ecdsa.Rfc6979.AArch64.p224Verify hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP224.AArch64
