module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P521.X86
import VerifiedGarbage.Proof.EcKey.X86.P521.Verified
import VerifiedGarbage.Proof.EcKey.X86.P521.Lit
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.X86.TaintMono
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
import VerifiedGarbage.Proof.P521.X86.Law
import VerifiedGarbage.Proof.EcKey.Compressed.X86.P521
import VerifiedGarbage.Proof.EcKey.Compressed.X86.P521Decompress
import VerifiedGarbage.Proof.EcKey.X86.P521.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-521 public keys (FIPS 186-5 §A.2) on x86 -/

namespace VG.Artifacts.EcP521.X86

open VG.Proof.P521.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.compressP521
    verified := Proof.EcKey.X86.P521.Scrub.compress_scrubbed },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.decompressP521
    verified := Proof.EcKey.X86.P521.Scrub.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.publicKeyP521
    verified := Proof.EcKey.X86.P521.Scrub.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP521.X86
