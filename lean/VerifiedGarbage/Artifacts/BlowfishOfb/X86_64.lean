module

public import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ofb, verified := .scrubbed Proof.Blowfish.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ofb_spSafe },
  Spec.Blowfish.ofbFinalApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ofbFinal, verified := .scrubbed Proof.Blowfish.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.BlowfishOfb.X86_64
