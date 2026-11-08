module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Proof.P384.GTable9 -- shake: keep (the artifacts' bodies use `gtabOk9`)
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.CoZTable
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P384.AArch64.Law

/-! # ECDSA over P-384 (FIPS 186-5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Verify.AArch64.verifyP384
    stack := 80
    verified := Proof.Ecdsa.Verify.AArch64.P384.verifyHash_verified hasLaw.law hasLaw.prime hasLaw.inv (Proof.P384.gtabOk9 hasLaw.law) }]

end VG.Artifacts.EcdsaP384.AArch64
