import VerifiedGarbage.Proof.Blowfish.X86_64.CbcVerified

/-! # Blowfish-CBC artifacts on baseline x86-64 -/

namespace VG.Artifacts.BlowfishCbc.X86_64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_blowfish_ecb_encrypt`'s block code (inlined): \
  each S-box lookup scans every entry of the box in SSE2 registers, so no address depends on the key or \
  the data; the schedule is read where it is. The mode is the generic CBC of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.Blowfish.cbcEncryptApi with
    target := X86_64.target
    doc := Spec.Blowfish.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcEncrypt
    contract := Spec.Blowfish.cbcEncryptContract X86_64.abi 96
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blowfish.cbcDecryptApi with
    target := X86_64.target
    doc := Spec.Blowfish.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcDecrypt
    contract := Spec.Blowfish.cbcDecryptContract X86_64.abi 96
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.BlowfishCbc.X86_64
