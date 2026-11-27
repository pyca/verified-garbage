module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
import VerifiedGarbage.Impl.Camellia.X86_64.Fn
import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CFB128 on x86-64 -/

namespace VG.Artifacts.CamelliaCfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Camellia.cfbEncryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbEncrypt, verified := Proof.Camellia.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Camellia.cfbDecryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbDecrypt, verified := Proof.Camellia.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbEncryptFinal, verified := Proof.Camellia.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbDecryptFinal, verified := Proof.Camellia.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbDecryptFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.CamelliaCfb.X86_64
