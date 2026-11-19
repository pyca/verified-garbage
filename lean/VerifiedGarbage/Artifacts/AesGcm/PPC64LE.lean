module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # AES-GCM (NIST SP 800-38D) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesGcm.PPC64LE

open VG.Proof.AesGcm.PPC64LE.Scrub

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact PPC64LE.target initReg,
  Spec.Gcm.streamInitApi.artifact PPC64LE.target streamInitReg,
  Spec.Gcm.streamAadApi.artifact PPC64LE.target streamAadReg,
  Spec.Gcm.streamEncryptApi.artifact PPC64LE.target streamEncryptReg,
  Spec.Gcm.streamDecryptApi.artifact PPC64LE.target streamDecryptReg,
  Spec.Gcm.streamFinishApi.artifact PPC64LE.target streamFinishReg,
  Spec.Gcm.streamVerifyApi.artifact PPC64LE.target streamVerifyReg,
  Spec.Gcm.sealApi.artifact PPC64LE.target sealReg,
  Spec.Gcm.openApi.artifact PPC64LE.target openReg,
  Spec.Gcm.sealGatherApi.artifact PPC64LE.target sealGatherReg,
  Spec.Gcm.openToApi.artifact PPC64LE.target openToReg]

end VG.Artifacts.AesGcm.PPC64LE
