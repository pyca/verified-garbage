module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Impl.Cast5.X86_64.Fn
import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CFB64 on x86-64 -/

namespace VG.Artifacts.Cast5Cfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Cast5.cfbEncryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbEncrypt, verified := Proof.Cast5.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Cast5.cfbDecryptApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbDecrypt, verified := Proof.Cast5.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbEncryptFinal, verified := Proof.Cast5.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.cfbDecryptFinal, verified := Proof.Cast5.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.cfbDecryptFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.Cast5Cfb.X86_64
