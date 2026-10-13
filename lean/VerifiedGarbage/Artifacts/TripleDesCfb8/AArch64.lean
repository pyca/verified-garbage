module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified

/-! # Triple DES-CFB8 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.AArch64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic CFB8 of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.cfb8EncryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.cfb8EncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfb8Encrypt
    contract := Spec.TripleDes.cfb8EncryptContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfb8Encrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.cfb8DecryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.cfb8DecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfb8Decrypt
    contract := Spec.TripleDes.cfb8DecryptContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfb8Decrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesCfb8.AArch64
