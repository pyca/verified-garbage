module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.AArch64

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline AArch64: a single-block scalar Feistel core with the S-box resident in NEON registers. \
  Table loads use fixed public addresses; secret indices select bytes only within registers. \
  The raw expanded keys and constant table are prepared once per call. Generic CFB retains \
  the IV pointer in x19, which the core preserves."

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncrypt
    stack := 3344
    verified := Proof.Camellia.AArch64.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecrypt
    stack := 3344
    verified := Proof.Camellia.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.AArch64
