module

public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5 key expansion and ECB on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact X86_64.target {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.X86_64.expandKey
    stack := 0
    verified := Proof.Cast5.X86_64.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact X86_64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86_64.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.X86_64.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact X86_64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86_64.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.X86_64.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.X86_64
