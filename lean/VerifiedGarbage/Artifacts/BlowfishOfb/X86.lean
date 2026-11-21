module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit

/-! # Blowfish-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.X86

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ofb
    verified := Proof.Blowfish.X86.Scrub.ofb_scrubbed },
  Spec.Blowfish.ofbFinalApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ofbFinal
    verified := Proof.Blowfish.X86.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.BlowfishOfb.X86
