module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CFB8 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.AArch64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic CFB8 of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfb8Encrypt
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfb8Encrypt_framed },
  Spec.TripleDes.cfb8DecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfb8Decrypt
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfb8Decrypt_framed }]

end VG.Artifacts.TripleDesCfb8.AArch64
