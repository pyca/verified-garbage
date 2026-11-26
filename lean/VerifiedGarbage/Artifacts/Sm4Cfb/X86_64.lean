module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Impl.Sm4.X86_64.Fn
import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CFB128 on x86-64 -/

namespace VG.Artifacts.Sm4Cfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sm4.cfbEncryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbEncrypt, verified := Proof.Sm4.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Sm4.cfbDecryptApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbDecrypt, verified := Proof.Sm4.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Sm4.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbEncryptFinal, verified := Proof.Sm4.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Sm4.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Sm4.X86_64.Fn.cfbDecryptFinal, verified := Proof.Sm4.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Sm4.X86_64.Scrub.cfbDecryptFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sm4Cfb.X86_64
