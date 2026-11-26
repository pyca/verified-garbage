module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.X86.Scrub
import VerifiedGarbage.Impl.Ed448.X86.Fn
import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
import VerifiedGarbage.Proof.Ed448.X86.VerifyEquationOk
import VerifiedGarbage.Proof.Ed448.X86.Verify.Verified
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.VerifyCT
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.X86.VerifyS
import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed448 (RFC 8032) on x86 -/

namespace VG.Artifacts.Ed448.X86

open VG.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Ed448.publicKeyApi.artifact X86.target {
    code := Impl.Ed448.X86.Fn.publicKey
    verified := Proof.Ed448.X86.Scrub.publicKey_scrubbed },
  Spec.Ed448.signCachedApi.artifact X86.target {
    code := Impl.Ed448.X86.Fn.signCached
    verified := Proof.Ed448.X86.Scrub.signCached_scrubbed },
  Spec.Ed448.verifyApi.artifact X86.target {
    code := Impl.Ed448.X86.Fn.verify
    verified := Proof.Ed448.X86.Scrub.verify_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ed448.X86
