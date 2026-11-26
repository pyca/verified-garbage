module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Verified
import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Sum
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.P192.AArch64.Law
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P192
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-192 (FIPS 186-5) on AArch64 -/

-- Deterministic ECDSA (RFC 6979) over P-192 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP192.AArch64.Rfc6979

open VG.Proof.P192.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.p192 hashes
    verified := Proof.Ecdsa.Rfc6979.AArch64.p192Sign_scrubbed hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcdsaP192.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.P192.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.P192.Joint.Fn.verifyHash
    verified := Proof.Ecdsa.Rfc6979.AArch64.p192Verify hasLaw.law hasLaw.inv }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP192.AArch64
