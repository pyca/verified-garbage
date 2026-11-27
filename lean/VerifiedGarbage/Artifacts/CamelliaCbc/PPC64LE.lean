module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CBC on PPC64LE -/

namespace VG.Artifacts.CamelliaCbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Camellia.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cbcEnc
    verified := Proof.Camellia.PPC64LE.Scrub.cbcEnc_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cbcDec
    verified := Proof.Camellia.PPC64LE.Scrub.cbcDec_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCbc.PPC64LE
