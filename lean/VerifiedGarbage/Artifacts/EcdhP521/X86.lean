module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P521.X86
public import VerifiedGarbage.Proof.Ecdh.X86.P521.Verified
import VerifiedGarbage.Proof.Ecdh.X86.P521.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86.Inv
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
public import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.Weierstrass.X86.Bits
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
public import VerifiedGarbage.Proof.Weierstrass.X86.Rep
public import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P521.X86.Law

/-! # ECDH over P-521 (SP 800-56A) on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.EcdhP521.X86

open VG.Proof.P521.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact X86.target {
    code := Impl.Ecdh.X86.exchangeP521
    stack := 28
    verified := Proof.Ecdh.X86.P521.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP521.X86
