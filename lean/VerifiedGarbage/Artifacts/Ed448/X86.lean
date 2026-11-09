module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
public import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Ed448.X86.VerifyEquationOk
public import VerifiedGarbage.Proof.Ed448.X86.Verify.Verified
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
public import VerifiedGarbage.Impl.Sha256.X86.Stream
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
public import VerifiedGarbage.Proof.Ed448.DecodeBytes
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Recover
public import VerifiedGarbage.Proof.Ed448.ScalarWords
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Ed448.VerifyFormulas
public import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
public import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.X86.VerifyCT
public import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
public import VerifiedGarbage.Proof.Ed448.X86.VerifyS
public import VerifiedGarbage.Proof.Ed448.X86.VerifySign
public import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Framework.X86.Sse
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
public import VerifiedGarbage.Proof.Sha512.Spec
public import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
public import VerifiedGarbage.Proof.X25519.X86.Basic
public import VerifiedGarbage.Proof.X448.Bytes
public import VerifiedGarbage.Proof.X448.X86.Carry
public import VerifiedGarbage.Proof.X448.X86.Columns
public import VerifiedGarbage.Proof.X448.X86.Copy
public import VerifiedGarbage.Proof.X448.X86.Counters
public import VerifiedGarbage.Proof.X448.X86.Decode
public import VerifiedGarbage.Proof.X448.X86.FnVerified
public import VerifiedGarbage.Proof.X448.X86.Frame
public import VerifiedGarbage.Proof.X448.X86.Freeze
public import VerifiedGarbage.Proof.X448.X86.Restore
public import VerifiedGarbage.Proof.X448.X86.Select
public import VerifiedGarbage.Proof.X448.X86.Small
public import VerifiedGarbage.Proof.X448.X86.Step

/-! # Ed448 (RFC 8032) on x86 -/

@[expose] public section

-- Ed448 public-key derivation on x86 (32-bit)
namespace VG.Artifacts.Ed448.X86.PublicKey

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact X86.target {
    code := Impl.Ed448.X86.PublicKey.code Impl.Ed448.X86.scalarBase
    stack := 280
    verified := Proof.Ed448.X86.PublicKey.publicKey_verified Proof.Ed448.X86.scalarBase_calleeOk }]

end VG.Artifacts.Ed448.X86.PublicKey

-- Ed448 signing with a cached public key on x86 (32-bit)
namespace VG.Artifacts.Ed448.X86.SignCached

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.signCachedApi.artifact X86.target {
    code := Impl.Ed448.X86.SignCached.code Impl.Ed448.X86.scalarBase
    stack := 280
    verified := Proof.Ed448.X86.SignCached.signCached_verified Proof.Ed448.X86.scalarBase_calleeOk }]

end VG.Artifacts.Ed448.X86.SignCached

-- Ed448 verification on x86 (32-bit)
namespace VG.Artifacts.Ed448.X86.Verify

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact X86.target {
    code := Impl.Ed448.X86.Verify.code Impl.Ed448.X86.verifyEquation
    stack := 280
    verified := Proof.Ed448.X86.Verify.verify_verified Proof.Ed448.X86.verifyEquation_calleeOk }]

end VG.Artifacts.Ed448.X86.Verify

namespace VG.Artifacts.Ed448.X86

def artifacts : List Artifact :=
  PublicKey.artifacts ++
  SignCached.artifacts ++
  Verify.artifacts

end VG.Artifacts.Ed448.X86
