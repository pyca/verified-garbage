module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Impl.EcKey.P384.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P384.Verified
public import VerifiedGarbage.Proof.EcKey.X86_64.P384.Lit
public import VerifiedGarbage.Proof.EcKey.X86_64.P384.VerifiedAdx
public import VerifiedGarbage.Proof.EcKey.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.Mont.X86_64.Blocks
public import VerifiedGarbage.Proof.Mont.X86_64.CsubS
public import VerifiedGarbage.Proof.Mont.X86_64.Friendly
public import VerifiedGarbage.Proof.Mont.X86_64.Ops
public import VerifiedGarbage.Proof.Mont.X86_64.Round
public import VerifiedGarbage.Proof.Mont.X86_64.Sparse
public import VerifiedGarbage.Proof.Mont.X86_64.SparseX
public import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
public import VerifiedGarbage.Proof.Mont.X86_64.WideOps
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P384.X86_64.Law
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P384Decompress

/-! # P-384 public keys (FIPS 186-5 §A.2) on x86-64 -/

@[expose] public section

-- Standalone P384 public-point compression on x86-64
namespace VG.Artifacts.EcP384.X86_64.Compressed

open VG.Proof.P384.X86_64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Compressed.X86_64.Fn.compress Impl.Ecdsa.X86_64.p384
      verified := .scrubbed (Proof.EcKey.Compressed.X86_64.P384.scrubbed hasLaw.inv false)
      spSafe := Proof.EcKey.Compressed.X86_64.P384.spSafe false },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Compressed.X86_64.Fn.decompress Impl.Ecdsa.X86_64.p384
      verified := .scrubbed (Proof.EcKey.Compressed.X86_64.P384Decompress.scrubbed hasLaw.law hasLaw.inv false)
      spSafe := Proof.EcKey.Compressed.X86_64.P384Decompress.spSafe false },
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.Compressed.X86_64.Fn.compress Impl.Ecdsa.X86_64.p384x
      verified := .scrubbed (Proof.EcKey.Compressed.X86_64.P384.scrubbed hasLaw.inv true)
      spSafe := Proof.EcKey.Compressed.X86_64.P384.spSafe true },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.Compressed.X86_64.Fn.decompress Impl.Ecdsa.X86_64.p384x
      verified := .scrubbed (Proof.EcKey.Compressed.X86_64.P384Decompress.scrubbed hasLaw.law hasLaw.inv true)
      spSafe := Proof.EcKey.Compressed.X86_64.P384Decompress.spSafe true }]

end VG.Artifacts.EcP384.X86_64.Compressed

-- Standalone P384 public-key validation on x86-64
namespace VG.Artifacts.EcP384.X86_64.Validate

open VG.Proof.P384.X86_64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.validatePublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Validate.X86_64.Fn.validate Impl.Ecdsa.X86_64.p384
      verified := .scrubbed (Proof.EcKey.Validate.X86_64.P384.scrubbed hasLaw.inv false)
      spSafe := Proof.EcKey.Validate.X86_64.P384.spSafe false },
  Spec.EcKey.P384.inst.validatePublicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.Validate.X86_64.Fn.validate Impl.Ecdsa.X86_64.p384x
      verified := .scrubbed (Proof.EcKey.Validate.X86_64.P384.scrubbed hasLaw.inv true)
      spSafe := Proof.EcKey.Validate.X86_64.P384.spSafe true }]

end VG.Artifacts.EcP384.X86_64.Validate

namespace VG.Artifacts.EcP384.X86_64

open VG.Proof.P384.X86_64 (hasLaw)

def artifacts : List Artifact :=
  Compressed.artifacts ++ [
  Spec.EcKey.P384.publicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.X86_64.Fn.publicKeyP384
      verified := .scrubbed (Proof.EcKey.X86_64.P384.publicKey_scrubbed hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv)
      spSafe := Proof.EcKey.X86_64.P384.publicKey_spSafe },
  Spec.EcKey.P384.publicKeyApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.EcKey.X86_64.Fn.publicKeyP384Adx
      verified := .scrubbed (Proof.EcKey.X86_64.P384.publicKeyAdx_scrubbed hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv)
      spSafe := Proof.EcKey.X86_64.P384.publicKeyAdx_spSafe }] ++
  Validate.artifacts

end VG.Artifacts.EcP384.X86_64
