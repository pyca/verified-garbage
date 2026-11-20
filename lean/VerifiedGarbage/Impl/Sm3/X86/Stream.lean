module

public import VerifiedGarbage.Impl.Sm3.X86
public import VerifiedGarbage.Impl.MdStream.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# Streaming SM3: x86 (32-bit) implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`). Every argument is on the stack
(cdecl).

* `init(state)` stores `IV`.
* `update(state, count, data, len, scratch)` and
  `finalize(state, count, out, scratch)` are the generic streaming code of
  `Impl/MdStream/X86.lean`, calling `vg_sm3_compress`
  (`Impl.Sm3.X86.compress`) with `scratch[0..112)` as its scratch space; our
  caller's callee-saved registers are saved after it, and `finalize` keeps
  `count` and `out` after them. The length field is big-endian, and so are
  the words of the hash value.
-/

@[expose] public section

namespace VG.Impl.Sm3.X86.Stream

open VG.X86
open VG.Impl.Sm3.X86 (at_ compress)
open VG.Impl.MdStream.X86 (Params len64 out32)

def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block ((List.range 8).flatMap fun k =>
      [.mov .ecx (.imm Spec.Sm3.iv[k]!), .store (at_ .eax (4 * k)) .ecx]))

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := len64 112 88 true
  out := out32 8 true

def update : Prog isa := MdStream.X86.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.X86.finalize params "vg_sm3_compress" compress

end VG.Impl.Sm3.X86.Stream

/-! ## The functions as emitted

Each function, then its cleanup: `init`, which calls nothing and has no
frame, then the clearing of the registers a callee may change
(`Impl.Scrub.X86.scrub 0`); `update` and `finalize`, in a frame of their own
(`withStackScratch`), then the zeroing of the `W` bytes of stack below `esp`
that they and the compression function use and that clearing
(`Impl.Scrub.X86.scrubF 0 W`), so that each returns without secret residue. -/

namespace VG.Impl.Sm3.X86.Fn

open VG.X86

/-- `vg_sm3_init`, as emitted. -/
def init : Prog isa := Impl.Scrub.X86.scrub 0 Stream.init

/-- `vg_sm3_update`, as emitted. -/
def update : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratch 188 5 Stream.update)

/-- `vg_sm3_finalize`, as emitted. -/
def finalize : Prog isa :=
  Impl.Scrub.X86.scrubF 0 204 (Impl.StackScratch.X86.withStackScratch 184 4 Stream.finalize)

end VG.Impl.Sm3.X86.Fn
