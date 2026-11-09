module

public import VerifiedGarbage.Impl.Sha256.X86_64
public import VerifiedGarbage.Impl.Sha256.X86_64.ShaNi
public import VerifiedGarbage.Impl.Sha256.X86_64.Avx2
public import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# Streaming SHA-256: x86-64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = rdi)` stores `H⁽⁰⁾` (`init224`, SHA-224's), with two 16-byte stores.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest;
  `finalize224` writes only its first 28 bytes, SHA-224's digest.

`update` and `finalize` are the generic streaming code of
`Impl/MdStream/X86_64.lean`. They take the compression function they call (a
`Callee`, e.g. `vg_sha256_compress` or `vg_sha256_compress_shani`), and are
emitted once for each implementation
(`Generic/MdHash/X86_64/Stream.lean`). It is called with
`scratch[0..560)` as its scratch space; our caller's callee-saved registers
are saved in `scratch[560..608)`. The length field is big-endian, and so are
the words of the digest. (HMAC-SHA256 calls the compression function and
saves registers the same way: `saved`, `save`, `restore` and `compressAt`.)
-/

@[expose] public section

namespace VG.Impl.Sha256.X86_64.Stream

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_ compress)

/-- A compression function to call: its symbol and its code. -/
structure Callee where
  name : String
  code : Prog isa

def Callee.scalar : Callee := ⟨"vg_sha256_compress", compress⟩
def Callee.shani : Callee := ⟨"vg_sha256_compress_shani", ShaNi.compress⟩
def Callee.avx2 : Callee := ⟨"vg_sha256_compress_avx2", Avx2.compress⟩

/-- Stores the initial hash value `iv`, sixteen bytes at a time (so that a
16-byte load of it right after is forwarded from the stores): words
`4q … 4q+3` are built in `xmm0` from two 64-bit immediates. -/
def initWith (iv : Spec.Sha256.HashValue) : Prog isa :=
  .block ((List.range 2).flatMap fun q =>
    [.movImm64 .rax (iv[4 * q + 1]! ++ iv[4 * q]!), .xop (.movq .xmm0 .rax),
      .movImm64 .rax (iv[4 * q + 3]! ++ iv[4 * q + 2]!), .xop (.movq .xmm1 .rax),
      .xop (.bin .punpcklqdq .xmm0 .xmm1), .movdquStore (at_ .rdi (16 * q)) .xmm0])

/-- `vg_sha256_init`. -/
def init : Prog isa := initWith Spec.Sha256.H0

/-- `vg_sha224_init`. -/
def init224 : Prog isa := initWith Spec.Sha256.H0_224

/-- The sizes, the length field and the digest. -/
def params : MdStream.X86_64.Params where
  N := 32
  B := 64
  L := 8
  so := 560
  len := MdStream.X86_64.len64 88 true
  lenV := MdStream.X86_64.lenV64 true
  out := MdStream.X86_64.out32 8 true

def update (f : Callee) : Prog isa := MdStream.X86_64.update params f.name f.code

def finalize (f : Callee) : Prog isa := MdStream.X86_64.finalize params f.name f.code

/-- SHA-224 outputs the first 28 bytes of the final hash value: `params`
with a digest of 7 words. -/
def params224 : MdStream.X86_64.Params := { params with out := MdStream.X86_64.out32 7 true }

def finalize224 (f : Callee) : Prog isa := MdStream.X86_64.finalize params224 f.name f.code

end VG.Impl.Sha256.X86_64.Stream
