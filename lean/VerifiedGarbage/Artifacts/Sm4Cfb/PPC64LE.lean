module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit

/-! # SM4-CFB128 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbEncrypt
    verified := .scrubbed Proof.Sm4.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbDecrypt
    verified := .scrubbed Proof.Sm4.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Sm4.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Sm4.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.Sm4Cfb.PPC64LE
