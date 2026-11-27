module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Spec.EcKey.Validate
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Impl.EcKey.P521.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
import VerifiedGarbage.Proof.EcKey.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.EcKey.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.P521.X86_64.Law
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P521
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P521
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P521Decompress
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-521 public keys (FIPS 186-5 §A.2) on x86-64 -/

-- Standalone P521 public-point compression on x86-64
namespace VG.Artifacts.EcP521.X86_64.Compressed

open VG.Proof.P521.X86_64 (hasLaw)

def artifacts : List (Artifact X86_64.target) := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Compressed.X86_64.Fn.compress Impl.Ecdsa.X86_64.p521
      verified := Proof.EcKey.Compressed.X86_64.P521.scrubbed hasLaw.inv false
      spSafe := Proof.EcKey.Compressed.X86_64.P521.spSafe false },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Compressed.X86_64.Fn.decompress Impl.Ecdsa.X86_64.p521
      verified := Proof.EcKey.Compressed.X86_64.P521Decompress.scrubbed hasLaw.law hasLaw.inv false
      spSafe := Proof.EcKey.Compressed.X86_64.P521Decompress.spSafe false },
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.Compressed.X86_64.Fn.compress Impl.Ecdsa.X86_64.p521x
      verified := Proof.EcKey.Compressed.X86_64.P521.scrubbed hasLaw.inv true
      spSafe := Proof.EcKey.Compressed.X86_64.P521.spSafe true },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.Compressed.X86_64.Fn.decompress Impl.Ecdsa.X86_64.p521x
      verified := Proof.EcKey.Compressed.X86_64.P521Decompress.scrubbed hasLaw.law hasLaw.inv true
      spSafe := Proof.EcKey.Compressed.X86_64.P521Decompress.spSafe true }]

end VG.Artifacts.EcP521.X86_64.Compressed

-- Standalone P521 public-key validation on x86-64
namespace VG.Artifacts.EcP521.X86_64.Validate

open VG.Proof.P521.X86_64 (hasLaw)

def artifacts : List (Artifact X86_64.target) := [
  Spec.EcKey.P521.inst.validatePublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Validate.X86_64.Fn.validate Impl.Ecdsa.X86_64.p521
      verified := Proof.EcKey.Validate.X86_64.P521.scrubbed hasLaw.inv false
      spSafe := Proof.EcKey.Validate.X86_64.P521.spSafe false },
  Spec.EcKey.P521.inst.validatePublicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.Validate.X86_64.Fn.validate Impl.Ecdsa.X86_64.p521x
      verified := Proof.EcKey.Validate.X86_64.P521.scrubbed hasLaw.inv true
      spSafe := Proof.EcKey.Validate.X86_64.P521.spSafe true }]

end VG.Artifacts.EcP521.X86_64.Validate

namespace VG.Artifacts.EcP521.X86_64

open VG.Proof.P521.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) :=
  Compressed.artifacts ++ [
  Spec.EcKey.P521.publicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.X86_64.Fn.publicKeyP521
      verified := Proof.EcKey.X86_64.P521.publicKey_scrubbed hasLaw.law (Proof.P521.combOk7 hasLaw.law) hasLaw.inv
      spSafe := Proof.EcKey.X86_64.P521.publicKey_spSafe },
  Spec.EcKey.P521.publicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.X86_64.Fn.publicKeyP521Adx
      verified := Proof.EcKey.X86_64.P521.publicKeyAdx_scrubbed hasLaw.law (Proof.P521.combOk7 hasLaw.law) hasLaw.inv
      spSafe := Proof.EcKey.X86_64.P521.publicKeyAdx_spSafe }] ++
  Validate.artifacts

spec_apis artifacts

end VG.Artifacts.EcP521.X86_64
