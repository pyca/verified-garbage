module

public import VerifiedGarbage.Impl.Md5.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# Streaming MD5: AArch64 implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`).

* `init(state = x0)` stores the initial MD buffer.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_md5_compress`).
-/

@[expose] public section

namespace VG.Impl.Md5.AArch64.Stream

open VG.AArch64
open VG.Impl.Md5.AArch64 (compress)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.movz .w .x9 (Spec.Md5.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Md5.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := MdStream.AArch64.len64 72 false
  out := MdStream.AArch64.out32 4 false

def update : Prog isa := MdStream.AArch64.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_md5_compress" compress

/-! ## The functions, as emitted

`vg_md5_update` and `vg_md5_finalize` with their 112 bytes of working space
in a frame on the stack, then their cleanup
(`Impl.Residue.AArch64.scrubAll`): the registers they write that the calling
convention does not preserve are cleared and their 128 bytes of stack
zeroed, so that they return without secret residue. -/

namespace Fn

/-- `vg_md5_update`, as emitted. -/
def update : Prog isa :=
  Residue.AArch64.scrubAll 128 0
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [], []⟩
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 Stream.update)

/-- `vg_md5_finalize`, as emitted. -/
def finalize : Prog isa :=
  Residue.AArch64.scrubAll 128 0
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [], []⟩
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 Stream.finalize)

end Fn

end VG.Impl.Md5.AArch64.Stream
