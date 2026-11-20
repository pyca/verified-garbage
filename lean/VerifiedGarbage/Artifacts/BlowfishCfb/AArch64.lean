module

public import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit

/-! # Blowfish-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbEncrypt
    verified := .scrubbed Proof.Blowfish.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Blowfish.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbDecrypt
    verified := .scrubbed Proof.Blowfish.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Blowfish.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Blowfish.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

end VG.Artifacts.BlowfishCfb.AArch64
