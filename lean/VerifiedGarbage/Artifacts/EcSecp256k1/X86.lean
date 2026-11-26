module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Impl.EcKey.Secp256k1.X86
import VerifiedGarbage.Proof.EcKey.X86.Secp256k1.Verified
import VerifiedGarbage.Proof.EcKey.X86.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.EcKey.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
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
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Secp256k1.X86.Law
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Secp256k1
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Secp256k1Decompress
import VerifiedGarbage.Proof.EcKey.X86.Secp256k1.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on x86 -/

namespace VG.Artifacts.EcSecp256k1.X86

open VG.Proof.Secp256k1.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.compressSecp256k1
    verified := Proof.EcKey.X86.Secp256k1.Scrub.compress_scrubbed hasLaw.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.decompressSecp256k1
    verified := Proof.EcKey.X86.Secp256k1.Scrub.decompress_scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.publicKeySecp256k1
    verified := Proof.EcKey.X86.Secp256k1.Scrub.publicKey_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcSecp256k1.X86
