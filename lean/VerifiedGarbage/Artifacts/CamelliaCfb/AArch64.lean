module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.AArch64

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers (the S-boxes as Boolean circuits), with no table lookups, in a batch of eight of which \
  the other seven are unused; the subkeys are prepared once per call. The mode is the generic CFB of \
  `Impl/Modes/AArch64/`, over Camellia's ECB core, with the IV's address kept in a vector register across the \
  core's code."

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.cfbEncrypt
    stack := 3248
    verified := Proof.Camellia.AArch64.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.cfbDecrypt
    stack := 3248
    verified := Proof.Camellia.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.AArch64
