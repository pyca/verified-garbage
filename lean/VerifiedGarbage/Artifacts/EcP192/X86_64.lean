module

import VerifiedGarbage.Proof.EcKey.X86_64.P192.Lit
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.EcKey.X86_64.P192.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
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
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P192.X86_64.Law
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P192Decompress

/-! # p192 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

-- Standalone P192 public-point compression on x86-64
namespace VG.Artifacts.EcP192.X86_64.Compressed

open VG.Proof.P192.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.P192

def artifacts : List Artifact :=
  [Spec.EcKey.P192.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 },
    Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.P192Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.P192Decompress.verified hasLaw.law hasLaw.inv false
      stack := 8 }]

end VG.Artifacts.EcP192.X86_64.Compressed

-- Standalone P192 public-key validation on x86-64
namespace VG.Artifacts.EcP192.X86_64.Validate

open VG.Proof.P192.X86_64 (hasLaw)
open VG.Proof.EcKey.Validate.X86_64.P192

def artifacts : List Artifact :=
  [Spec.EcKey.P192.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 }]

end VG.Artifacts.EcP192.X86_64.Validate

namespace VG.Artifacts.EcP192.X86_64

open VG.Proof.P192.X86_64 (hasLaw)

def artifacts : List Artifact :=
  Compressed.artifacts ++
  [
    Spec.EcKey.P192.publicKeyApi.artifact X86_64.target {
      code := Impl.EcKey.X86_64.publicKeyP192
      stack := 8
      verified := Proof.EcKey.X86_64.P192.pk_verified hasLaw.law hasLaw.inv }] ++
  Validate.artifacts

end VG.Artifacts.EcP192.X86_64
