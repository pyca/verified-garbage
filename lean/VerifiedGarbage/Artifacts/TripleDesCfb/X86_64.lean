module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Scrub
import VerifiedGarbage.Proof.Variants.TripleDesEcb.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB64 on x86-64 -/

namespace VG.Artifacts.TripleDesCfb.X86_64

def direct : List (Artifact X86_64.target) := [
  Spec.TripleDes.cfbEncryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfbEncrypt, verified := Proof.TripleDes.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfbEncryptFinal, verified := Proof.TripleDes.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfbDecryptFinal, verified := Proof.TripleDes.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.TripleDesCfb.X86_64

namespace VG.Artifacts.TripleDesCfb.X86_64

open VG.Proof.TripleDes.X86_64.Batch (EcbImpl)

public def artifacts : List (Artifact X86_64.target) :=
  direct ++
  (VG.Proof.Variants.TripleDesEcb.X86_64.variants.flatMap fun (v : EcbImpl) => [
    Spec.TripleDes.cfbDecryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.TripleDes.X86_64.Fn.cfbDecrypt v.level (v.name .encrypt) (v.code .encrypt)
      verified := Proof.TripleDes.X86_64.Batch.Scrub.cfbDecrypt_scrubbed v
      spSafe := Proof.TripleDes.X86_64.Batch.Scrub.cfbDecrypt_spSafe v }])

spec_apis artifacts

end VG.Artifacts.TripleDesCfb.X86_64
