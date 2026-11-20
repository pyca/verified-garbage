module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit

/-! # Camellia-CFB128 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbEnc
    verified := .scrubbed Proof.Camellia.PPC64LE.Scrub.cfbEnc_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbDec
    verified := .scrubbed Proof.Camellia.PPC64LE.Scrub.cfbDec_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbEncFinal
    verified := .scrubbed Proof.Camellia.PPC64LE.Scrub.cfbEncFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Camellia.PPC64LE.Fn.cfbDecFinal
    verified := .scrubbed Proof.Camellia.PPC64LE.Scrub.cfbDecFinal_scrubbed }]

end VG.Artifacts.CamelliaCfb.PPC64LE
