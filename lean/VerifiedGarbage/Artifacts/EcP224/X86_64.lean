module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Impl.EcKey.P224.X86_64
public import VerifiedGarbage.Proof.EcKey.X86_64.P224.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.Law
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
public import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
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
public import VerifiedGarbage.Proof.P224.X86_64.Law
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P224
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P224Decompress

/-! # P-224 public keys (FIPS 186-5 §A.2) on x86-64 -/

@[expose] public section

-- Standalone P224 public-point compression on x86-64
namespace VG.Artifacts.EcP224.X86_64.Compressed

open VG.Proof.P224.X86_64 (hasLaw)
open VG.Proof.EcKey.Compressed.X86_64.P224

def artifacts : List Artifact :=
  [Spec.EcKey.P224.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 },
    Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.P224Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.P224Decompress.verified hasLaw.law hasLaw.inv false
      stack := 8 }]

end VG.Artifacts.EcP224.X86_64.Compressed

-- Standalone P224 public-key validation on x86-64
namespace VG.Artifacts.EcP224.X86_64.Validate

open VG.Proof.P224.X86_64 (hasLaw)
open VG.Proof.EcKey.Validate.X86_64.P224

def artifacts : List Artifact :=
  [Spec.EcKey.P224.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 }]

end VG.Artifacts.EcP224.X86_64.Validate

namespace VG.Artifacts.EcP224.X86_64

open VG.Proof.P224.X86_64 (hasLaw)

def artifacts : List Artifact :=
  Compressed.artifacts ++
  [
    Spec.EcKey.P224.publicKeyApi.artifact X86_64.target {
      code := Impl.EcKey.X86_64.publicKeyP224
      stack := 8
      verified := Proof.EcKey.X86_64.P224.pk_verified hasLaw.law (Proof.P224.combOk7 hasLaw.law) hasLaw.inv }] ++
  Validate.artifacts

end VG.Artifacts.EcP224.X86_64
