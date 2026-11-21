module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cbcEncrypt
    verified := Proof.Sm4.PPC64LE.Scrub.cbcEncrypt_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Sm4.PPC64LE.Fn.cbcDecrypt
    verified := Proof.Sm4.PPC64LE.Scrub.cbcDecrypt_scrubbed }]

end VG.Artifacts.Sm4Cbc.PPC64LE
