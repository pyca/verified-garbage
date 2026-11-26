module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Impl.Ecdh.P256.X86
import VerifiedGarbage.Proof.Ecdh.X86.Verified
import VerifiedGarbage.Proof.Ecdh.X86.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.X86.JacLayout
import VerifiedGarbage.Proof.Ecdh.X86.JacMain
import VerifiedGarbage.Proof.Ecdh.X86.JacMul
import VerifiedGarbage.Proof.Ecdh.X86.JacPow
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.WinFinish
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacLoop
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.P256.X86.Law
import VerifiedGarbage.Proof.Ecdh.X86.P256.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-256 (SP 800-56A) on x86 -/

namespace VG.Artifacts.EcdhP256.X86

open VG.Proof.P256.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.Ecdh.P256.exchangeApi.artifact X86.target {
    code := Impl.Ecdh.X86.Fn.exchangeP256
    verified := Proof.Ecdh.X86.P256.Scrub.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime }]

spec_apis artifacts

end VG.Artifacts.EcdhP256.X86
