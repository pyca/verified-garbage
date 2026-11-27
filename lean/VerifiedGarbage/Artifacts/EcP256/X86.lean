module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.X86.CombVerified
import VerifiedGarbage.Proof.EcKey.X86.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.X86.CombContract
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.EcKey.X86.CombMain
import VerifiedGarbage.Proof.EcKey.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P256.X86
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.P256.X86.Law
import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256
import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256Decompress
import VerifiedGarbage.Proof.EcKey.X86.P256.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-256 public keys (FIPS 186-5 §A.2) on x86 -/

namespace VG.Artifacts.EcP256.X86

open VG.Proof.P256.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.compressP256
    verified := Proof.EcKey.X86.P256.Scrub.compress_scrubbed hasLaw.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.decompressP256
    verified := Proof.EcKey.X86.P256.Scrub.decompress_scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P256.publicKeyApi.artifact X86.target {
    code := Impl.EcKey.X86.Fn.publicKeyP256
    verified := Proof.EcKey.X86.P256.Scrub.publicKey_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcP256.X86
