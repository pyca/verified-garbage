module

public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
public import VerifiedGarbage.Proof.Cast5.X86.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # CAST5-CFB64 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncrypt
    stack := 336
    verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.X86.ModeFns.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecrypt
    stack := 336
    verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.X86.ModeFns.cfbDecrypt_framed },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncryptFinal
    stack := 336
    verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecryptFinal
    stack := 336
    verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.Cast5Cfb.X86
