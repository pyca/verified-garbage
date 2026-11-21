module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit

/-! # Blowfish-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cbcEncryptChained
    verified := Proof.Blowfish.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.cbcDecryptChained
    verified := Proof.Blowfish.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.BlowfishCbc.X86
