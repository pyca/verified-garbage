module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Init
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-OCB (RFC 7253) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are emitted.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there.

An AES-OCB key context is an AES-GCM one (the key schedule, then the
encrypted zero block at byte 240), so `init` is AES-GCM's code, in its frame
of 2592 bytes holding its working space (`Proof/AesOcb/PPC64LE/Init.lean`).
`seal` and `open` run in a frame of 2688 bytes holding theirs and a copy of
their stack arguments `tag` and `tag_len` (`Proof/AesOcb/PPC64LE/Frame.lean`);
the functions they call use no stack.
-/

@[expose] public section

namespace VG.Artifacts.AesOcb.PPC64LE

open VG.Proof.AesOcb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init
    stack := 2592
    verified := init_framed },
  Spec.Ocb.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«seal»
    stack := 2688
    verified := seal_framed },
  Spec.Ocb.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«open»
    stack := 2688
    verified := open_framed }]

end VG.Artifacts.AesOcb.PPC64LE
