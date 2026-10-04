import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesOcb.X86_64.Verified

/-!
# AES-OCB (RFC 7253) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and
`vg_aes_expand_key`, are emitted once for each implementation
(`Variants/AesBlocks/X86_64/`), named with its suffix (e.g.
`vg_aes_ocb_seal_aesni`), and need its CPU features.

The stack is 8 bytes for each: the return address of their calls, whose
callees use no stack; `seal` and `open` also read their arguments after the
sixth, from the data to the tag's length, from the stack above their return
address.
-/

namespace VG.Generic.AesBlocks.X86_64.AesOcb

open VG.Proof.AesOcb.X86_64

/-- Which functions an instance calls. -/
def callNote (v : Proof.Aes.X86_64.BlocksImpl) (dec : Bool) : String :=
  "This implementation enciphers with `" ++ v.enc.name ++ "`" ++
    (if dec then ", and deciphers with `" ++ v.dec.name ++ "`." else ".")

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  { Spec.Ocb.initApi with
    name := Spec.Ocb.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ocb.initApi.doc (notes := ["This implementation expands the key with `" ++ v.expand.name ++
      "`, and enciphers `L_*` with `" ++ v.enc.name ++ "`."])
    code := Impl.AesOcb.X86_64.init (callees v)
    contract := Spec.Ocb.initContract X86_64.abi 8
    stack := 8
    verified := init_verified v
    spSafe := init_spSafe v
    features := v.features },
  { Spec.Ocb.sealApi with
    name := Spec.Ocb.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ocb.sealApi.doc (notes := [callNote v false])
    code := Impl.AesOcb.X86_64.seal (callees v)
    contract := Spec.Ocb.sealContract X86_64.abi 8
    stack := 8
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.Ocb.openApi with
    name := Spec.Ocb.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ocb.openApi.doc (notes := [callNote v true,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesOcb.X86_64.open (callees v)
    contract := Spec.Ocb.openContract X86_64.abi 8
    stack := 8
    verified := open_verified v
    spSafe := open_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOcb
