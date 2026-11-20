module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP320r1.Joint.Verified
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP320r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP320r1.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP320r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP320r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP320r1.Sum
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.AArch64.Law
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP320r1
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on AArch64 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP320r1 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP320r1.AArch64.Rfc6979

open VG.Proof.BrainpoolP320r1.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.brainpoolp320r1 hashes
    verified := .scrubbed (Proof.Ecdsa.Rfc6979.AArch64.brainpoolp320r1Sign_scrubbed hasLaw.law hasLaw.inv) }]

end VG.Artifacts.EcdsaBrainpoolP320r1.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP320r1.AArch64

open VG.Proof.BrainpoolP320r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.BrainpoolP320r1.Joint.Fn.verifyHash
    verified := .scrubbed (Proof.Ecdsa.Rfc6979.AArch64.brainpoolp320r1Verify hasLaw.law hasLaw.inv) }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP320r1.AArch64
