module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit

/-! # CAST5-CFB64 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact PPC64LE.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt
    stack := 208
    verified := Proof.Cast5.PPC64LE.Modes.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact PPC64LE.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt
    stack := 208
    verified := Proof.Cast5.PPC64LE.Modes.cfbDecrypt_framed }]

end VG.Artifacts.Cast5Cfb.PPC64LE
