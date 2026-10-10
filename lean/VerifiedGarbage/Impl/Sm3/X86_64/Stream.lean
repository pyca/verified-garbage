import VerifiedGarbage.Impl.Sm3.X86_64
import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# Streaming SM3: x86-64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`).

* `init(state = rdi)` stores `IV`.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the hash
  value.

`update` and `finalize` are the generic streaming code of
`Impl/MdStream/X86_64.lean`, calling `vg_sm3_compress`
(`Impl.Sm3.X86_64.compress`) with `scratch[0..576)` as its scratch space;
our caller's callee-saved registers are saved in `scratch[576..624)`. The
length field is big-endian, and so are the words of the hash value.
-/

namespace VG.Impl.Sm3.X86_64.Stream

open VG.X86_64
open VG.Impl.Sm3.X86_64 (at_ compress)
open VG.Impl.MdStream.X86_64 (Params len64 out32)

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.mov32 .rax (.imm Spec.Sm3.iv[k]!), .store32 (at_ .rdi (4 * k)) .rax])

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 32
  B := 64
  L := 8
  so := 576
  len := len64 88 true
  out := out32 8 true

def update : Prog isa := MdStream.X86_64.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.X86_64.finalize params "vg_sm3_compress" compress

end VG.Impl.Sm3.X86_64.Stream
