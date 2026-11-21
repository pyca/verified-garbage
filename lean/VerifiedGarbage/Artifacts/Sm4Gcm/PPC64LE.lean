module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.PPC64LE

open VG.Proof.Sm4Gcm.PPC64LE.Scrub

def artifacts : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.init
    verified := init_scrubbed },
  Spec.Sm4.Gcm.sealApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.seal
    verified := seal_scrubbed },
  Spec.Sm4.Gcm.openApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.open
    verified := open_scrubbed },
  Spec.Sm4.Gcm.streamInitApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.streamInit
    verified := streamInit_scrubbed },
  Spec.Sm4.Gcm.streamAadApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.streamAad
    verified := streamAad_scrubbed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.streamEncrypt
    verified := streamEncrypt_scrubbed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.streamDecrypt
    verified := streamDecrypt_scrubbed },
  Spec.Sm4.Gcm.streamFinishApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.streamFinish
    verified := streamFinish_scrubbed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact PPC64LE.target {
    code := Impl.Sm4Gcm.PPC64LE.Fn.streamVerify
    verified := streamVerify_scrubbed }]

end VG.Artifacts.Sm4Gcm.PPC64LE
