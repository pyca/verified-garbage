module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit

/-! # CAST5-CFB64 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt
    stack := 208
    verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.PPC64LE.Modes.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt
    stack := 208
    verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.PPC64LE.Modes.cfbDecrypt_framed },
  Spec.Cast5.cfbEncryptFinalApi.artifact PPC64LE.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncryptFinal
    stack := 208
    verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.PPC64LE.FbFinal.cfbEncryptFinal_framed },
  Spec.Cast5.cfbDecryptFinalApi.artifact PPC64LE.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecryptFinal
    stack := 208
    verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.PPC64LE.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.Cast5Cfb.PPC64LE
