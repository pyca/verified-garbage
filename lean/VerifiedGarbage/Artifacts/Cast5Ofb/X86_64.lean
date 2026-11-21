module

public import VerifiedGarbage.Impl.Cast5.X86_64.Fn
public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit

/-! # CAST5-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ofb, verified := Proof.Cast5.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ofb_spSafe },
  Spec.Cast5.ofbFinalApi.artifact X86_64.target { code := Impl.Cast5.X86_64.Fn.ofbFinal, verified := Proof.Cast5.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Cast5.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.Cast5Ofb.X86_64
