module

public import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/AArch64/`, over Camellia's ECB core."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.cbcEncrypt
    stack := 3248
    verified := Proof.Camellia.AArch64.cbcEncrypt_framed },
  Spec.Camellia.cbcDecryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64: eight blocks at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/AArch64/`, over Camellia's ECB core."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.cbcDecrypt
    stack := 3248
    verified := Proof.Camellia.AArch64.cbcDecrypt_framed }]

end VG.Artifacts.CamelliaCbc.AArch64
