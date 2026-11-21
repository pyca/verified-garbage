module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalLit

/-! # Triple DES-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbEncrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbDecrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.TripleDesCfb.PPC64LE
