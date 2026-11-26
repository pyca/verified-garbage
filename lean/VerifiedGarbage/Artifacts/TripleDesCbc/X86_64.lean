module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Scrub
import VerifiedGarbage.Proof.Variants.TripleDesEcb.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CBC on x86-64 -/

namespace VG.Artifacts.TripleDesCbc.X86_64

def direct : List (Artifact X86_64.target) := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cbcEncrypt, verified := Proof.TripleDes.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cbcEncrypt_spSafe }]

end VG.Artifacts.TripleDesCbc.X86_64

namespace VG.Artifacts.TripleDesCbc.X86_64

open VG.Proof.TripleDes.X86_64.Batch (EcbImpl)

public def artifacts : List (Artifact X86_64.target) :=
  direct ++
  (VG.Proof.Variants.TripleDesEcb.X86_64.variants.flatMap fun (v : EcbImpl) => [
    Spec.TripleDes.cbcDecryptChainedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.TripleDes.X86_64.Fn.cbcDecrypt v.level (v.name .decrypt) (v.code .decrypt)
      verified := Proof.TripleDes.X86_64.Batch.Scrub.cbcDecrypt_scrubbed v
      spSafe := Proof.TripleDes.X86_64.Batch.Scrub.cbcDecrypt_spSafe v }])

spec_apis artifacts

end VG.Artifacts.TripleDesCbc.X86_64
