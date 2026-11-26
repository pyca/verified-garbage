module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Verified
import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Sum
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.BrainpoolP384r1.AArch64.Law
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on AArch64 -/

-- Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP384r1.AArch64.Rfc6979

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.brainpoolp384r1 hashes
    verified := Proof.Ecdsa.Rfc6979.AArch64.brainpoolp384r1Sign_scrubbed hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcdsaBrainpoolP384r1.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP384r1.AArch64

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Fn.verifyHash
    verified := Proof.Ecdsa.Rfc6979.AArch64.brainpoolp384r1Verify hasLaw.law hasLaw.inv }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaBrainpoolP384r1.AArch64
