module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Verified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Camellia on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Camellia.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.expandKey
    verified := Proof.Camellia.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ecbEnc
    verified := Proof.Camellia.PPC64LE.Scrub.ecbEnc_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.ecbDec
    verified := Proof.Camellia.PPC64LE.Scrub.ecbDec_scrubbed }]

end VG.Artifacts.Camellia.PPC64LE
