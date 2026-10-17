module

public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.AArch64

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table \
  lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is \
  built once per call, by a call of `vg_sm4_prepare_keys`, and each batch is a call of `vg_sm4_crypt_prepared`. The mode is the generic CFB of `Impl/Modes/AArch64/`, over SM4's ECB core, with the IV's \
  address kept in a vector register across the core's code."

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbEncrypt
    stack := 3264
    verified := Proof.Sm4.AArch64.cfbEncrypt_framed },
  Spec.Sm4.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbDecrypt
    stack := 3264
    verified := Proof.Sm4.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.Sm4Cfb.AArch64
