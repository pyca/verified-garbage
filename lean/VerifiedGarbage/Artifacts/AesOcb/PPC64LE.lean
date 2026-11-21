module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-OCB (RFC 7253) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOcb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact PPC64LE.target {
    code := Impl.AesOcb.PPC64LE.Fn.init
    verified := Proof.AesOcb.PPC64LE.Scrub.init_scrubbed },
  Spec.Ocb.sealApi.artifact PPC64LE.target {
    code := Impl.AesOcb.PPC64LE.Fn.seal
    verified := Proof.AesOcb.PPC64LE.Scrub.seal_scrubbed },
  Spec.Ocb.openApi.artifact PPC64LE.target {
    code := Impl.AesOcb.PPC64LE.Fn.open
    verified := Proof.AesOcb.PPC64LE.Scrub.open_scrubbed }]

end VG.Artifacts.AesOcb.PPC64LE
