module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.P384.GTable9
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.P384.AArch64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P384
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-384 (FIPS 186-5) on AArch64 -/

-- Deterministic ECDSA (RFC 6979) over P-384 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP384.AArch64.Rfc6979

open VG.Proof.P384.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.p384 hashes
    verified := Proof.Ecdsa.Rfc6979.AArch64.p384Sign_scrubbed hasLaw.law hasLaw.inv (Proof.P384.combOk7 hasLaw.law) }]

end VG.Artifacts.EcdsaP384.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.P384.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP384
    verified := Proof.Ecdsa.Rfc6979.AArch64.p384Verify hasLaw.law hasLaw.prime hasLaw.inv (Proof.P384.gtabOk9 hasLaw.law) }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP384.AArch64
