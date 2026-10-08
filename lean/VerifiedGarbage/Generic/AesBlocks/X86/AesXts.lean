import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesXts.X86.Verified

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/X86/`), named
with its suffix (e.g. `vg_aes_xts_encrypt_aesni`), and need its CPU
features.

The stack is 24 bytes: the five arguments of the block function and the
return address of its call.
-/

namespace VG.Generic.AesBlocks.X86.AesXts

open VG.Proof.AesXts.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  { Spec.Xts.aesEncryptApi with
    name := Spec.Xts.aesEncryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Xts.aesEncryptApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesXts.X86.encrypt v.enc
    contract := Spec.Xts.aesEncryptContract X86.abi 24
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  { Spec.Xts.aesDecryptApi with
    name := Spec.Xts.aesDecryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Xts.aesDecryptApi.doc (notes := ["This implementation deciphers one block at a time with `" ++
      v.dec.name ++ "`."])
    code := Impl.AesXts.X86.decrypt v.dec
    contract := Spec.Xts.aesDecryptContract X86.abi 24
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesXts
