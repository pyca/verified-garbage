module

public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CFB64 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncrypt
    stack := 336
    verified := Proof.Cast5.X86.ModeFns.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecrypt
    stack := 336
    verified := Proof.Cast5.X86.ModeFns.cfbDecrypt_framed }]

end VG.Artifacts.Cast5Cfb.X86
