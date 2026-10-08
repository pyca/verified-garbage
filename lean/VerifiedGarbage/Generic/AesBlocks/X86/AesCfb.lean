import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesCfb.X86.Verified

/-!
# AES-CFB128 (NIST SP 800-38A §6.3) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` (both directions use the
forward cipher), are emitted once for each implementation
(`Variants/AesBlocks/X86/`), named with its suffix (e.g.
`vg_aes_cfb128_encrypt_aesni`), and need its CPU features.

The stack is 24 bytes: the five arguments of the block function and the
return address of its call.
-/

namespace VG.Generic.AesBlocks.X86.AesCfb

open VG.Proof.AesCfb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  { Spec.Cfb.aesEncryptApi with
    name := Spec.Cfb.aesEncryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cfb.aesEncryptApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesCfb.X86.encrypt v.enc
    contract := Spec.Cfb.aesEncryptContract X86.abi 24
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  { Spec.Cfb.aesDecryptApi with
    name := Spec.Cfb.aesDecryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cfb.aesDecryptApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesCfb.X86.decrypt v.enc
    contract := Spec.Cfb.aesDecryptContract X86.abi 24
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCfb
