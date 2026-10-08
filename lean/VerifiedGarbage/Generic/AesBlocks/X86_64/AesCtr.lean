import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesCtr.X86_64.Verified

/-!
# AES-CTR (NIST SP 800-38A §6.5) on x86-64

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, is emitted once for each
implementation (`Variants/AesBlocks/X86_64/`), named with its suffix (e.g.
`vg_aes_ctr_aesni`), and needs its CPU features.

The stack is 8 bytes: the return address of the call of the block function,
which uses no stack.
-/

namespace VG.Generic.AesBlocks.X86_64.AesCtr

open VG.Proof.AesCtr.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  { Spec.Ctr.aesApi with
    name := Spec.Ctr.aesApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ctr.aesApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesCtr.X86_64.crypt v.enc
    contract := Spec.Ctr.aesContract X86_64.abi 8
    stack := 8
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesCtr
