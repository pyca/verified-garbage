module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
import Mathlib.Tactic.SplitIfs

/-! # SM4-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, encrypted bitsliced in general-purpose registers through the AES S-box \
  circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of eight of which the other \
  seven are unused; the key schedule's table of round keys is built once per call. The mode is the generic CFB of \
  `Impl/Modes/X86/`, over SM4's ECB core."

def artifacts : List Artifact := [
  { Spec.Sm4.cfbEncryptApi with
    target := X86.target
    doc := Spec.Sm4.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 Impl.Sm4.X86.cfbEncrypt
    contract := Spec.Sm4.cfbEncryptContract X86.abi 1472
    stack := 1472
    verified := Proof.Sm4.X86.Fb.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm4.cfbDecryptApi with
    target := X86.target
    doc := Spec.Sm4.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 Impl.Sm4.X86.cfbDecrypt
    contract := Spec.Sm4.cfbDecryptContract X86.abi 1472
    stack := 1472
    verified := Proof.Sm4.X86.Fb.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sm4Cfb.X86
