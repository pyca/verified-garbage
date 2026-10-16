module

public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Registration

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
of 3632 bytes for `seal` and `open` (3584 bytes of working space, which
includes the table of `L_j`), which also holds a copy of their four other
stack arguments (`Verified.stackArgScratch`).
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesOcb

open VG.Proof.AesOcb.X86_64

/-- Which functions an instance calls. -/
def callNote (v : Proof.Aes.X86_64.BlocksImpl) (dec : Bool) : String :=
  "This implementation enciphers with `" ++ v.enc.name ++ "`" ++
    (if dec then ", and deciphers with `" ++ v.dec.name ++ "`." else ".")

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Ocb.initApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation expands the key with `" ++ v.expand.name ++
      "`, and enciphers `L_*` with `" ++ v.enc.name ++ "`."]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init (callees v))
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := v.features },
  Spec.Ocb.sealApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [callNote v false]
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.seal (callees v))
    stack := 3640
    verified := seal_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Ocb.openApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [callNote v true,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.open (callees v))
    stack := 3640
    verified := open_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOcb
