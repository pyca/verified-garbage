module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdh.P384
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P384.AArch64.Law

/-! # ECDH over P-384 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.exchangeP384
    verified := Proof.Ecdh.AArch64.P384.ecdh_verified hasLaw.law hasLaw.inv hasLaw.prime }]

end VG.Artifacts.EcdhP384.AArch64
