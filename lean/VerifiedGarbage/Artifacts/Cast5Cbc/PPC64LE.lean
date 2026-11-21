module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit

/-! # CAST5-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Cast5.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Cast5.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Cast5Cbc.PPC64LE
