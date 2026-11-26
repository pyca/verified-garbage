module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P224.X86
import VerifiedGarbage.Proof.EcKey.X86.P224.Verified
import VerifiedGarbage.Proof.EcKey.X86.P224.Lit
import VerifiedGarbage.Proof.Framework.Registration
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintSum
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
import VerifiedGarbage.Proof.P224.X86.Law
import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224
import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224Decompress
import VerifiedGarbage.Proof.EcKey.X86.P224.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-224 public keys (FIPS 186-5 §A.2) on x86 -/

namespace VG.Artifacts.EcP224.X86

open VG.Proof.P224.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.compressP224
    verified := Proof.EcKey.X86.P224.Scrub.compress_scrubbed },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.decompressP224
    verified := Proof.EcKey.X86.P224.Scrub.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.publicKeyP224
    verified := Proof.EcKey.X86.P224.Scrub.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP224.X86
