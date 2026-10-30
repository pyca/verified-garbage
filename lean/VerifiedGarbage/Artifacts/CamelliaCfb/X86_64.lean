module

public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit

/-! # Camellia-CFB128 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.X86_64
