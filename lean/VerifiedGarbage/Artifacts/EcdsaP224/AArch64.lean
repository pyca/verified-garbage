module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P224.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P224.AArch64.Law
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # ECDSA over P-224 (FIPS 186-5) on AArch64 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-224 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaP224.AArch64.Rfc6979

open VG.Proof.P224.AArch64 (hasLaw)
open VG.Proof.HmacTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact AArch64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.AArch64.Fn.p224 hashes
    verified := Proof.Ecdsa.Rfc6979.AArch64.p224Sign_scrubbed hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) }]

end VG.Artifacts.EcdsaP224.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP224
    verified := Proof.Ecdsa.Rfc6979.AArch64.p224Verify hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP224.AArch64
