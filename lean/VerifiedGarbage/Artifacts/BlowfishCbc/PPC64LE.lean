module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit

/-! # Blowfish-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Blowfish.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Blowfish.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.BlowfishCbc.PPC64LE
