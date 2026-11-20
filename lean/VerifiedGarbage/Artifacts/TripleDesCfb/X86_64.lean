module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Scrub
public import VerifiedGarbage.Proof.Variants.TripleDesEcb.X86_64

/-! # Triple DES-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86_64

def direct : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfbEncrypt, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfbEncryptFinal, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfbDecryptFinal, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.TripleDesCfb.X86_64

namespace VG.Artifacts.TripleDesCfb.X86_64

open VG.Proof.TripleDes.X86_64.Batch (EcbImpl)

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.TripleDesEcb.X86_64.variants.flatMap fun (v : EcbImpl) => [
    Spec.TripleDes.cfbDecryptApi.artifact X86_64.target (Proof.TripleDes.X86_64.Batch.Scrub.cfbDecryptReg v)])

end VG.Artifacts.TripleDesCfb.X86_64
