module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P384.X86
import VerifiedGarbage.Proof.Ecdh.X86.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86.P384.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.P384.X86.Law
import VerifiedGarbage.Proof.Ecdh.X86.P384.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-384 (SP 800-56A) on x86 -/

namespace VG.Artifacts.EcdhP384.X86

open VG.Proof.P384.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.Ecdh.P384.exchangeApi.artifact X86.target {
    code := Impl.Ecdh.X86.Fn.exchangeP384
    verified := Proof.Ecdh.X86.P384.Scrub.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP384.X86
