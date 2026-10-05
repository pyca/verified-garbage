import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesOcb.X86_64.Frame

/-!
# AES-OCB (RFC 7253) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and
`vg_aes_expand_key_scratch`, are emitted once for each implementation
(`Variants/AesBlocks/X86_64/`), named with its suffix (e.g.
`vg_aes_ocb_seal_aesni`), and need its CPU features.

The code of each uses 8 bytes of stack: the return address of its calls,
whose callees use no stack; `seal` and `open` also read their arguments
after the sixth, from the data to the working space, from the stack above
their return address. Each keeps its working space, its last argument, in a
frame on the stack: of 2568 bytes for `init` (`Verified.stackScratch`), and
of 2608 bytes for `seal` and `open`, which also holds a copy of their four
other stack arguments (`Verified.stackArgScratch`).
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
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init (callees v))
    contract := Spec.Ocb.initContract X86_64.abi 2576
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (init_spSafe v)
    features := v.features },
  { Spec.Ocb.sealApi with
    name := Spec.Ocb.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ocb.sealApi.doc (notes := [callNote v false])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesOcb.X86_64.seal (callees v))
    contract := Spec.Ocb.sealContract X86_64.abi 2616
    stack := 2616
    verified := seal_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := v.features },
  { Spec.Ocb.openApi with
    name := Spec.Ocb.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ocb.openApi.doc (notes := [callNote v true,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesOcb.X86_64.open (callees v))
    contract := Spec.Ocb.openContract X86_64.abi 2616
    stack := 2616
    verified := open_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOcb
