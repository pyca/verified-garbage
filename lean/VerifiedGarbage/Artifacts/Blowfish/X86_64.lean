module
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit

public import VerifiedGarbage.Proof.Blowfish.X86_64.Frame
public import VerifiedGarbage.Proof.Blowfish.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey
    stack := 40
    verified := Proof.Blowfish.X86_64.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.encrypt
    stack := 264
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.decrypt
    stack := 264
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.decrypt_verified }]

end VG.Artifacts.Blowfish.X86_64
