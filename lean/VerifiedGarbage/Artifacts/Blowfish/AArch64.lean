module

public import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
public import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.Residue
public import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Blowfish on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.expandKey
    verified := .scrubbed Proof.Blowfish.AArch64.expandKeyCleared_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.ecbEncrypt
    verified := .scrubbed Proof.Blowfish.AArch64.ModesResidue.ecbEncryptCode_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.ecbDecrypt
    verified := .scrubbed Proof.Blowfish.AArch64.ModesResidue.ecbDecryptCode_scrubbed }]

end VG.Artifacts.Blowfish.AArch64
