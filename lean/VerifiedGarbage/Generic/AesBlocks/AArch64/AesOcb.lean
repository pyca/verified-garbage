module

public import VerifiedGarbage.Proof.AesOcb.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-OCB (RFC 7253) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and
`vg_aes_expand_key_scratch`, are emitted once for each implementation
(`Variants/AesBlocks/AArch64/`), named with its suffix (e.g.
`vg_aes_ocb_seal_aes`), and need its CPU features.

The functions' calls (`bl`) keep the return address in `x30`, which they
save, with the registers they use, in their working space (`work` or
`scratch`), so their code uses no stack; `seal` and `open` read their last
three arguments, `tag`, `tag_len` and `work`, from the stack. Each keeps its
working space, its last argument, in a frame on the stack: of 2560 bytes for
`init` (`Verified.stackScratch`), and of 2592 bytes for `seal` and `open`,
which also holds a copy of `tag` and `tag_len` (`Verified.stackArgScratch`).
-/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesOcb

open VG.Proof.AesOcb.AArch64

/-- Which functions an instance calls. -/
def callNote (v : Proof.Aes.AArch64.BlocksImpl) (dec : Bool) : String :=
  "This implementation enciphers with `" ++ v.enc.name ++ "`" ++
    (if dec then ", and deciphers with `" ++ v.dec.name ++ "`." else ".")

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Ocb.initApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation expands the key with `" ++ v.expand.name ++
      "`, and enciphers `L_*` with `" ++ v.enc.name ++ "`."]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (Impl.AesOcb.AArch64.init (callees v))
    stack := 2560
    verified := init_framed v
    features := v.features },
  Spec.Ocb.sealApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [callNote v false]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesOcb.AArch64.seal (callees v))
    stack := 2592
    verified := seal_framed v
    features := v.features },
  Spec.Ocb.openApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [callNote v true,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesOcb.AArch64.open (callees v))
    stack := 2592
    verified := open_framed v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesOcb
