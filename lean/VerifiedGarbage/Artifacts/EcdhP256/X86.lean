module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Impl.Ecdh.P256.X86
public import VerifiedGarbage.Proof.Ecdh.X86.Verified
public import VerifiedGarbage.Proof.Ecdh.X86.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdh.X86.JacLayout
public import VerifiedGarbage.Proof.Ecdh.X86.JacMain
public import VerifiedGarbage.Proof.Ecdh.X86.JacMul
public import VerifiedGarbage.Proof.Ecdh.X86.JacPow
public import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86.Finish
public import VerifiedGarbage.Proof.Ecdsa.X86.Inv
public import VerifiedGarbage.Proof.Ecdsa.X86.Middle
public import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
public import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
public import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.X86.Verified
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.P256.Order
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.JacState
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
public import VerifiedGarbage.Proof.Weierstrass.X86.Rep
public import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
public import VerifiedGarbage.Proof.Weierstrass.X86.TComb
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
public import VerifiedGarbage.Proof.Weierstrass.X86.WinFinish
public import VerifiedGarbage.Proof.Weierstrass.X86.WinJacLoop
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P256.X86.Law

/-! # ECDH over P-256 (SP 800-56A) on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.EcdhP256.X86

open VG.Proof.P256.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact X86.target {
    code := Impl.Ecdh.X86.exchangeP256
    stack := 28
    verified := Proof.Ecdh.X86.ecdh_verified hasLaw.law hasLaw.inv hasLaw.prime }]

end VG.Artifacts.EcdhP256.X86
