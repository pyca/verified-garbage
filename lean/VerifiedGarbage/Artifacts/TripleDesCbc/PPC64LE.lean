module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.TripleDes.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.TripleDes.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.TripleDesCbc.PPC64LE
