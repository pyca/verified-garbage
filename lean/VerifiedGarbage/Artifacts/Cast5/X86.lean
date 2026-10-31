module

public import VerifiedGarbage.Proof.Cast5.X86.KeyVerified
public import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5 key expansion and ECB on baseline 32-bit x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact X86.target {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.X86.expandKey
    stack := 4
    verified := Proof.Cast5.X86.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86.ecbEncrypt
    stack := 4
    verified := Proof.Cast5.X86.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86.ecbDecrypt
    stack := 4
    verified := Proof.Cast5.X86.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.X86
