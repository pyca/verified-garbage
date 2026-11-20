module

public import VerifiedGarbage.Impl.Sha1.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Writes
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64.OneShot

/-!
# Streaming SHA-1: AArch64 implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`).

* `init(state = x0)` stores the initial hash value.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_sha1_compress`).
-/

@[expose] public section

namespace VG.Impl.Sha1.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha1.AArch64 (compress)

def init : Prog isa :=
  .block ((List.range 5).flatMap fun k =>
    [.movz .w .x9 (Spec.Sha1.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sha1.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 20
  B := 64
  L := 8
  so := 112
  len := MdStream.AArch64.len64 76 true
  out := MdStream.AArch64.out32 5 true

def update : Prog isa := MdStream.AArch64.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sha1_compress" compress

/-! ## The functions, as emitted

Each streaming function over a compression function is its code with its
working space in a frame on the stack, then its cleanup
(`Impl.Residue.AArch64.scrubOf`), which clears the registers the code may
write, the compression function's included, and zeroes that stack, so that it
returns without secret residue. -/

namespace Fn

open VG.Impl.Residue.AArch64 (scrubOf)
open VG.Impl.StackScratch.AArch64 (withStackScratch)

/-- `vg_sha1_update` over the compression function `code`, its working space in a frame of its own. -/
def update (name : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 160) 0 (withStackScratch 160 .x4 (MdStream.AArch64.update params name code))

/-- `vg_sha1_finalize` over the compression function `code`, its working space in a frame of its own. -/
def finalize (name : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 160) 0 (withStackScratch 160 .x3 (MdStream.AArch64.finalize params name code))

/-- `vg_sha1_digest`, the one-shot digest over the compression function `code`, in its frame. -/
def digest (name : String) (code : Prog isa) : Prog isa :=
  scrubOf (MdStream.AArch64.OneShot.frameBytes params) 0
    (MdStream.AArch64.OneShot.digest params init name code)

end Fn

end VG.Impl.Sha1.AArch64.Stream
