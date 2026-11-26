module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.X86_64.VariantForLit
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ed448.X86_64.Scrub
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Variants.Curve448Field.X86_64
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
import VerifiedGarbage.Impl.Ed448.X86_64.SignCached
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Correct
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAdd
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.CT
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Correct
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Ed448.X86_64.Words57
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.X448.X86_64.Freeze
import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
import VerifiedGarbage.Impl.Ed448.X86_64.Verify
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed448 (RFC 8032) on x86-64 -/

-- Ed448 public-key derivation on x86-64
namespace VG.Artifacts.Ed448.X86_64.PublicKey

def artifactsFor (v : Impl.Ed448.X86_64.FieldVariant) : List (Artifact X86_64.target) := [
  Spec.Ed448.publicKeyApi.artifact X86_64.target
    { suffix := v.suffix
      code := Impl.Ed448.X86_64.Fn.publicKey v
      verified := Proof.Ed448.X86_64.Scrub.publicKey_scrubbed v
      spSafe := Proof.Ed448.X86_64.Scrub.publicKey_spSafe v }]

def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.Curve448Field.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448.X86_64.PublicKey

-- Ed448 signing with a cached public key on x86-64
namespace VG.Artifacts.Ed448.X86_64.SignCached

def artifactsFor (v : Impl.Ed448.X86_64.FieldVariant) : List (Artifact X86_64.target) := [
  Spec.Ed448.signCachedApi.artifact X86_64.target
    { suffix := v.suffix
      code := Impl.Ed448.X86_64.SignCached.Fn.signCached v
      verified := Proof.Ed448.X86_64.Scrub.signCached_scrubbed v
      spSafe := Proof.Ed448.X86_64.Scrub.signCached_spSafe v }]

def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.Curve448Field.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448.X86_64.SignCached

-- Ed448 verification on x86-64
namespace VG.Artifacts.Ed448.X86_64.Verify

def artifactsFor (v : Impl.Ed448.X86_64.FieldVariant) : List (Artifact X86_64.target) := [
  Spec.Ed448.verifyApi.artifact X86_64.target
    { suffix := v.suffix
      code := Impl.Ed448.X86_64.Verify.Fn.verify v
      verified := Proof.Ed448.X86_64.Scrub.verify_scrubbed v
      spSafe := Proof.Ed448.X86_64.Scrub.verify_spSafe v }]

def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.Curve448Field.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448.X86_64.Verify

namespace VG.Artifacts.Ed448.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  PublicKey.artifacts ++
  SignCached.artifacts ++
  Verify.artifacts

spec_apis artifacts

end VG.Artifacts.Ed448.X86_64
