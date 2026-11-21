module

public import VerifiedGarbage.Impl.Camellia.X86_64.Fn
public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit

/-! # Camellia-CFB128 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbEncrypt, verified := Proof.Camellia.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Camellia.cfbDecryptApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbDecrypt, verified := Proof.Camellia.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbEncryptFinal, verified := Proof.Camellia.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Camellia.X86_64.Fn.cfbDecryptFinal, verified := Proof.Camellia.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Camellia.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.CamelliaCfb.X86_64
