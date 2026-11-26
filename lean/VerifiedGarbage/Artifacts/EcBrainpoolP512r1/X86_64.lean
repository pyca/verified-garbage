module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.Validate
import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP512r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
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
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.BrainpoolP512r1.X86_64.Law
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.BrainpoolP512r1
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.BrainpoolP512r1
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.BrainpoolP512r1Decompress
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on x86-64 -/

-- Standalone BrainpoolP512r1 public-point compression on x86-64
namespace VG.Artifacts.EcBrainpoolP512r1.X86_64.Compressed

open VG.Proof.BrainpoolP512r1.X86_64 (hasLaw)

def artifacts : List (Artifact X86_64.target) :=
  [Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Compressed.X86_64.Fn.compress Impl.Ecdsa.X86_64.brainpoolp512r1
      verified := Proof.EcKey.Compressed.X86_64.BrainpoolP512r1.scrubbed hasLaw.inv
      spSafe := Proof.EcKey.Compressed.X86_64.BrainpoolP512r1.spSafe },
    Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact X86_64.target
      { code := Impl.EcKey.Compressed.X86_64.Fn.decompress Impl.Ecdsa.X86_64.brainpoolp512r1
        verified := Proof.EcKey.Compressed.X86_64.BrainpoolP512r1Decompress.scrubbed hasLaw.law hasLaw.inv
        spSafe := Proof.EcKey.Compressed.X86_64.BrainpoolP512r1Decompress.spSafe }]

end VG.Artifacts.EcBrainpoolP512r1.X86_64.Compressed

-- Standalone BrainpoolP512r1 public-key validation on x86-64
namespace VG.Artifacts.EcBrainpoolP512r1.X86_64.Validate

open VG.Proof.BrainpoolP512r1.X86_64 (hasLaw)

def artifacts : List (Artifact X86_64.target) :=
  [Spec.EcKey.BrainpoolP512r1.inst.validatePublicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.Validate.X86_64.Fn.validate Impl.Ecdsa.X86_64.brainpoolp512r1
      verified := Proof.EcKey.Validate.X86_64.BrainpoolP512r1.scrubbed hasLaw.inv
      spSafe := Proof.EcKey.Validate.X86_64.BrainpoolP512r1.spSafe }]

end VG.Artifacts.EcBrainpoolP512r1.X86_64.Validate

namespace VG.Artifacts.EcBrainpoolP512r1.X86_64

open VG.Proof.BrainpoolP512r1.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact X86_64.target
    { code := Impl.EcKey.X86_64.Fn.publicKeyBrainpoolP512r1
      verified := Proof.EcKey.X86_64.BrainpoolP512r1.publicKey_scrubbed hasLaw.law hasLaw.inv
      spSafe := Proof.EcKey.X86_64.BrainpoolP512r1.publicKey_spSafe }] ++
  Compressed.artifacts ++
  Validate.artifacts

spec_apis artifacts

end VG.Artifacts.EcBrainpoolP512r1.X86_64
