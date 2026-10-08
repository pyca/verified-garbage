import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesOfb.X86.Verified

/-!
# AES-OFB (NIST SP 800-38A §6.4) on x86

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, is emitted once for each
implementation (`Variants/AesBlocks/X86/`), named with its suffix (e.g.
`vg_aes_ofb_aesni`), and needs its CPU features.

The stack is 24 bytes: the five arguments of the block function and the
return address of its call.
-/

namespace VG.Generic.AesBlocks.X86.AesOfb

open VG.Proof.AesOfb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  { Spec.Ofb.aesApi with
    name := Spec.Ofb.aesApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Ofb.aesApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesOfb.X86.crypt v.enc
    contract := Spec.Ofb.aesContract X86.abi 24
    stack := 24
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesOfb
