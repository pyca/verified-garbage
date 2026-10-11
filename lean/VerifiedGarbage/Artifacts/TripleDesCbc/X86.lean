import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified

/-! # Triple DES-CBC artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.TripleDesCbc.X86

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, calling the verified block function (`vg_triple_des_encrypt_block` \
  or `vg_triple_des_decrypt_block`), with Boolean S-box circuits and no table lookups; the schedule is \
  copied into the working space once per call. The mode is the generic CBC of `Impl/Modes/X86/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.cbcEncryptApi with
    target := X86.target
    doc := Spec.TripleDes.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcEncrypt
    contract := Spec.TripleDes.cbcEncryptContract X86.abi 984
    stack := 984
    verified := Proof.TripleDes.X86.Cbc.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.cbcDecryptApi with
    target := X86.target
    doc := Spec.TripleDes.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcDecrypt
    contract := Spec.TripleDes.cbcDecryptContract X86.abi 984
    stack := 984
    verified := Proof.TripleDes.X86.Cbc.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.TripleDesCbc.X86
