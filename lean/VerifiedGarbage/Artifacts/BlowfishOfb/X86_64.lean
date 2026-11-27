module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Impl.Blowfish.X86_64.Fn
import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-OFB on x86-64 -/

namespace VG.Artifacts.BlowfishOfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Blowfish.ofbApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ofb, verified := Proof.Blowfish.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ofb_spSafe },
  Spec.Blowfish.ofbFinalApi.artifact X86_64.target { code := Impl.Blowfish.X86_64.Fn.ofbFinal, verified := Proof.Blowfish.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Blowfish.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.BlowfishOfb.X86_64
