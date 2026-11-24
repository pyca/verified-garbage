module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideVerified
public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3Wide
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideLit

/-! # Blowfish-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Fn.cbcEncryptChained
    verified := Proof.Blowfish.X86.Ssse3.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cbcEncryptChained
    verified := Proof.Blowfish.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Wide.Fn.cbcDecryptChained
    verified := Proof.Blowfish.X86.Ssse3.Wide.cbcDecryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cbcDecryptChained
    verified := Proof.Blowfish.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.BlowfishCbc.X86
