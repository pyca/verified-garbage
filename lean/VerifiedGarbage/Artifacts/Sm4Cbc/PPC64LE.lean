module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CBC on PPC64LE -/

namespace VG.Artifacts.Sm4Cbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sm4.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cbcEncrypt
    verified := Proof.Sm4.PPC64LE.Scrub.cbcEncrypt_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cbcDecrypt
    verified := Proof.Sm4.PPC64LE.Scrub.cbcDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cbc.PPC64LE
