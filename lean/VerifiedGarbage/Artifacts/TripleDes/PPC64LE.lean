module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Lit

/-! # Triple DES on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDes.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.expandKey
    verified := .scrubbed Proof.TripleDes.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.ecbEncrypt
    verified := .scrubbed Proof.TripleDes.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.ecbDecrypt
    verified := .scrubbed Proof.TripleDes.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.TripleDes.PPC64LE
