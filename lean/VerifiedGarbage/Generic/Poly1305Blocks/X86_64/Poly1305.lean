module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateCall
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Poly1305.Stream
public import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateCall

/-!
# Streaming Poly1305 (RFC 8439 §2.5) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which absorb the
whole blocks of the data with an implementation `v` of `vg_poly1305_blocks`,
are emitted once for each implementation (`Variants/Poly1305Blocks/X86_64/`),
named with its suffix (e.g. `vg_poly1305_update_avx2`), and need its CPU
features. `init` and `finalize` call no implementation of it, and are in the
registration file.

The stack is 160 bytes for every implementation: the frame of 136 bytes
holding the working space, the return address of the call of
`vg_poly1305_blocks`, and up to 16 bytes for its own calls.
-/

@[expose] public section

namespace VG.Generic.Poly1305Blocks.X86_64.Poly1305

open VG.Proof.Poly1305.X86_64 (BlocksImpl)

/-- Which implementation of `vg_poly1305_blocks` an instance calls. -/
def note (v : BlocksImpl) : String :=
  "This implementation absorbs the whole blocks of the data with `" ++ v.name ++
    "`, and saves its caller's callee-saved registers in its working space."

def artifacts (v : BlocksImpl) : List Artifact := [
  Spec.Poly1305.updateApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackScratch 136 .r8
      (Impl.Poly1305.X86_64.update v.name v.code)
    stack := 160
    verified := Proof.Poly1305.X86_64.update_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.Poly1305.X86_64.update_spSafe v)
    features := v.features }]

end VG.Generic.Poly1305Blocks.X86_64.Poly1305
