module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CFB128 on PPC64LE -/

namespace VG.Artifacts.CamelliaCfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Camellia.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbEnc
    verified := Proof.Camellia.PPC64LE.Scrub.cfbEnc_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbDec
    verified := Proof.Camellia.PPC64LE.Scrub.cfbDec_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbEncFinal
    verified := Proof.Camellia.PPC64LE.Scrub.cfbEncFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbDecFinal
    verified := Proof.Camellia.PPC64LE.Scrub.cfbDecFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCfb.PPC64LE
