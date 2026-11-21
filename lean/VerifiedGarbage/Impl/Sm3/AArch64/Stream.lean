module

public import VerifiedGarbage.Impl.Sm3.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Union

/-!
# Streaming SM3: AArch64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`).

* `init(state = x0)` stores `IV`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_sm3_compress`) with `scratch[0..64)` as its scratch space. The length
  field is big-endian, and so are the words of the hash value.
-/

@[expose] public section

namespace VG.Impl.Sm3.AArch64.Stream

open VG.AArch64
open VG.Impl.Sm3.AArch64 (compress)

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movz .w .x9 (Spec.Sm3.iv[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sm3.iv[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 32
  B := 64
  L := 8
  so := 64
  len := MdStream.AArch64.len64 88 true
  out := MdStream.AArch64.out32 8 true

def update : Prog isa := MdStream.AArch64.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sm3_compress" compress

/-! ## The functions, as emitted

`vg_sm3_update` and `vg_sm3_finalize` over an implementation of the
compression function, with their 112 bytes of working space in a frame on
the stack, then their cleanup (`Impl.Scrub.AArch64.scrubAll`): the
registers they write that the calling convention does not preserve are
cleared and their 128 bytes of stack zeroed, so that they return without
secret residue. The registers are those their own instructions write,
stated here, and those the compression function states it writes. -/

/-- An implementation of the compression function to call: its symbol, its
code, and the registers its code writes, of those the calling convention
does not preserve (the proofs hold it to the code,
`Proof.Sm3.AArch64.Compress.scrub`). -/
structure Compress where
  name : String
  code : Prog isa
  clear : Impl.Scrub.AArch64.Clear

namespace Fn

open VG.Impl.Scrub.AArch64 (Clear scrubAll)

/-- The registers `vg_sm3_update`'s own instructions write. -/
def updateOwn : Clear := ⟨[.x1, .x2, .x3, .x4, .x9, .x10, .x11, .x12, .x13, .x16, .x17], [], []⟩

/-- `vg_sm3_update`, as emitted. -/
def update (c : Compress) : Prog isa :=
  scrubAll 128 0 (updateOwn.union c.clear)
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 (MdStream.AArch64.update params c.name c.code))

/-- The registers `vg_sm3_finalize`'s own instructions write. -/
def finalizeOwn : Clear := ⟨[.x1, .x2, .x3, .x9, .x11, .x12, .x13, .x16, .x17], [], []⟩

/-- `vg_sm3_finalize`, as emitted. -/
def finalize (c : Compress) : Prog isa :=
  scrubAll 128 0 (finalizeOwn.union c.clear)
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 (MdStream.AArch64.finalize params c.name c.code))

end Fn

end VG.Impl.Sm3.AArch64.Stream
