module

public import VerifiedGarbage.Proof.AesOcb.X86.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.Conv

/-!
# AES-OCB (RFC 7253) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and
`vg_aes_expand_key_scratch`, are emitted once for each implementation
(`Variants/AesBlocks/X86/`), named with its suffix (e.g.
`vg_aes_ocb_seal_aesni`), and need its CPU features.

Each runs in a frame holding its working space and a copy of its stack
arguments (`Proof/AesOcb/X86/Frame.lean`): 2608 bytes for `seal` and `open`
(ten arguments), 2580 bytes for `init` (three), below which its calls use 24
bytes (their five arguments and return address; the callees use no stack).
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesOcb

open VG.Proof.AesOcb.X86

/-- Which functions an instance calls. -/
def callNote (v : Proof.Aes.X86.BlocksImpl) (dec : Bool) : String :=
  "This implementation enciphers with `" ++ v.enc.name ++ "`" ++
    (if dec then ", and deciphers with `" ++ v.dec.name ++ "`." else ".")

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ocb.initApi.artifact X86.target {
    suffix := v.suffix
    notes := ["This implementation expands the key with `" ++ v.expand.name ++
      "`, and enciphers `L_*` with `" ++ v.enc.name ++ "`."]
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesOcb.X86.init (callees v))
    stack := 2604
    verified := init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v)
    features := v.features },
  Spec.Ocb.sealApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v false]
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesOcb.X86.seal (callees v))
    stack := 2632
    verified := seal_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Ocb.openApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v true,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesOcb.X86.open (callees v))
    stack := 2632
    verified := open_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesOcb
