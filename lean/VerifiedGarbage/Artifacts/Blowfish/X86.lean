module

public import VerifiedGarbage.Proof.Blowfish.X86.Frame
import VerifiedGarbage.Proof.Blowfish.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish on baseline x86 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey
    stack := 84
    verified := Proof.Blowfish.X86.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.encrypt
    stack := 276
    verified := Proof.Blowfish.X86.ecb_framed true },
  Spec.Blowfish.ecbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.decrypt
    stack := 276
    verified := Proof.Blowfish.X86.ecb_framed false }]

end VG.Artifacts.Blowfish.X86
