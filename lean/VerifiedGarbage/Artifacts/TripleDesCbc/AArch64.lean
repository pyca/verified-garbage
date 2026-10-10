import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified

/-! # Triple DES-CBC artifacts on baseline AArch64 -/

namespace VG.Artifacts.TripleDesCbc.AArch64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block` \
  and `vg_triple_des_decrypt_block`'s code, inlined), with Boolean S-box circuits and no table lookups; \
  the schedule is copied into the working space once per call. The mode is the generic CBC of \
  `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cbcEncrypt
    contract := Spec.TripleDes.cbcEncryptContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cbcDecrypt
    contract := Spec.TripleDes.cbcDecryptContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesCbc.AArch64
