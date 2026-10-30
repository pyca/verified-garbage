module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-SIV (RFC 5297) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are emitted.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there.

`init` keeps its 2560-byte working space in a frame of 2592 bytes, and
`encrypt` and `decrypt` theirs, of 2576 bytes, in a frame of 2608
(`Proof/AesSiv/PPC64LE/Verified.lean`). A call (`bl`) stores nothing in
memory, and the functions they call use no stack: their `stack` is that
frame.
-/

@[expose] public section

namespace VG.Artifacts.AesSiv.PPC64LE

open VG.Proof.AesSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesSiv.PPC64LE.init
    stack := 2592
    verified := init_framed },
  Spec.Siv.encryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2608 .r10 Impl.AesSiv.PPC64LE.encrypt
    stack := 2608
    verified := encrypt_framed },
  Spec.Siv.decryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2608 .r10 Impl.AesSiv.PPC64LE.decrypt
    stack := 2608
    verified := decrypt_framed }]

end VG.Artifacts.AesSiv.PPC64LE
