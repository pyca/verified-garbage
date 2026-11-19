module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Verified
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Sum
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P192.AArch64.Law
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P192
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # ECDSA over P-192 (FIPS 186-5) on AArch64 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-192 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP192.AArch64.Rfc6979

open VG.Proof.P192.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT OK p192 p192T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifactsFor : List Artifact :=
  if hv : OK VG.Proof.Variants.MdHash.AArch64.variants then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := ""
      tables := [("hmac", tables VG.Proof.Variants.MdHash.AArch64.variants)]
      code := signCodeT (p192 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p192.tries VG.Proof.Variants.MdHash.AArch64.variants
      verified := p192T_verified hasLaw.law hasLaw.inv VG.Proof.Variants.MdHash.AArch64.variants hv } Proof.Ecdsa.Rfc6979.AArch64.p192SignClear
      (Proof.Ecdsa.Rfc6979.AArch64.Scrub.signOk
        Spec.Ecdsa.Rfc6979.Curves.p192 [] VG.Proof.Variants.MdHash.AArch64.variants)
      (Proof.Ecdsa.Rfc6979.AArch64.p192SignSide hasLaw.law hasLaw.inv))]
  else []

def artifacts : List Artifact :=
  artifactsFor

end VG.Artifacts.EcdsaP192.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Verify.AArch64.P192.Joint.verify
    verified := Proof.Ecdsa.Verify.AArch64.P192.Joint.verifyHash_verified hasLaw.law hasLaw.inv } Proof.Ecdsa.Rfc6979.AArch64.p192VerifyClear
    (Proof.EcKey.AArch64.Scrub.verifyHashOk _) Proof.Ecdsa.Rfc6979.AArch64.p192VerifySide)] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP192.AArch64
