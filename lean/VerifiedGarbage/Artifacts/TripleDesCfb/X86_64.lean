import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified

/-! # Triple DES-CFB64 artifacts on baseline x86-64 -/

namespace VG.Artifacts.TripleDesCfb.X86_64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic CFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.cfbEncryptApi with
    target := X86_64.target
    doc := Spec.TripleDes.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt
    contract := Spec.TripleDes.cfbEncryptContract X86_64.abi 976
    stack := 976
    verified := Proof.TripleDes.X86_64.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.cfbDecryptApi with
    target := X86_64.target
    doc := Spec.TripleDes.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecrypt
    contract := Spec.TripleDes.cfbDecryptContract X86_64.abi 976
    stack := 976
    verified := Proof.TripleDes.X86_64.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.TripleDesCfb.X86_64
