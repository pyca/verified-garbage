import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesCbc.X86.Verified

/-!
# AES-CBC (NIST SP 800-38A §6.2) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/X86/`), named
with its suffix (e.g. `vg_aes_cbc_encrypt_aesni`), and need its CPU
features.

The stack is 24 bytes: the five arguments of the block function and the
return address of its call.
-/

namespace VG.Generic.AesBlocks.X86.AesCbc

open VG.Proof.AesCbc.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  { Spec.Cbc.aesEncryptApi with
    name := Spec.Cbc.aesEncryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cbc.aesEncryptApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesCbc.X86.encrypt v.enc
    contract := Spec.Cbc.aesEncryptContract X86.abi 24
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  { Spec.Cbc.aesDecryptApi with
    name := Spec.Cbc.aesDecryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cbc.aesDecryptApi.doc (notes := ["This implementation deciphers one block at a time with `" ++
      v.dec.name ++ "`."])
    code := Impl.AesCbc.X86.decrypt v.dec
    contract := Spec.Cbc.aesDecryptContract X86.abi 24
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCbc
