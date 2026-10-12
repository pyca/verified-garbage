import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified

/-! # Triple DES-CFB64 artifacts on baseline AArch64 -/

namespace VG.Artifacts.TripleDesCfb.AArch64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic CFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.cfbEncryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfbEncrypt
    contract := Spec.TripleDes.cfbEncryptContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.cfbDecryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfbDecrypt
    contract := Spec.TripleDes.cfbDecryptContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesCfb.AArch64
