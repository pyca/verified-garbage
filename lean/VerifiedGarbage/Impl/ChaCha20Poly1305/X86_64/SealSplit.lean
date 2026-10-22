module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split

/-!
# ChaCha20-Poly1305 encryption with the data's first bytes read from another buffer: x86-64

`vg_chacha20_poly1305_seal_split(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, src_len = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24], work = [rsp + 32])` (`work` allocated on the stack by the
frame, as `seal`'s) is `seal` (`../X86_64.lean`) on the data at `dst` whose
first `src_len` bytes are read from `src` (`sealSplitFor`).

It first copies the bytes of `src` it does not read in place of the data's to
`dst` (`head`): `key`, `nonce`, `aad_len` and `src` wait in `work[0, 32)`,
which `seal` writes before it reads, while `SealGather.copyBytes` copies them.
Then it runs `seal` in a frame of 40 bytes laid out as `seal`'s entry
(`framed`): `tag` and `work` at `rsp + 8` and `rsp + 16`, `seal`'s stack
arguments, and `src` and `src_len` after them, at `rsp + 24` and `rsp + 32`,
with the data and its length in `r8` and `r9` (its own stack arguments are
read only).

With the AVX-512 implementations of `vg_poly1305_blocks` (`.avx512`,
`.ifma`, whose `seal` calls `vg_chacha20_xor_avx512`), it copies only the
first `m` bytes of `src` (or all of it if it is shorter), those that the
prologue's keystream covers (`m` as `seal` computes it, `foldM`: the whole
data if it is at most 960 bytes, else a multiple of 64), and runs `seal` but
for its call of `vg_chacha20_xor` on the data after them, which becomes the
code of `vg_chacha20_xor_split_avx512`, inline, with the bytes of `src` after
them (`cryptSplit`). So a TLS record of `n · 1024 + 1` bytes, its payload in
`src` and its content type already in `dst`, has only its first 64 bytes
copied. With the others, it copies all of `src` and runs the `seal` the
instance's `vg_chacha20_poly1305_seal` runs (`Stitch.sealFor`).

The branches are on the lengths only.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.X86_64.SealSplit

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width copyBytes)

/-- `work` into `rax`. A block of its own, so that the constant-time
analysis of the next, which addresses `work` through `rax`, starts from it
public. -/
def loadW : List Instr := [.mov .rax (.mem (at_ .rsp 32))]

/-- `key`, `nonce`, `aad_len` and `src` into `work[0, 32)` (at `rax`). -/
def stash : List Instr :=
  [.store (at_ .rax 0) .rdi, .store (at_ .rax 8) .rsi, .store (at_ .rax 16) .rcx, .store (at_ .rax 24) .r8]

/-- `rcx` = the number of bytes of `src` to copy: all of them (`whole`), or
at most `m`, the bytes the prologue's keystream covers for the `len` bytes
(in `r10`) of `seal` with `vg_chacha20_xor_avx512`: `len` if it is at most
960, else `len` modulo 1024 rounded up to a multiple of 64 if that is at
most 960, else 0 (`foldM 960 1024`). -/
def prefixLen : Bool → List Instr
  | true => [.mov .rcx (.reg .r9)]
  | false =>
    [.mov .r10 (.mem (at_ .rsp 16)), .mov .rcx (.reg .r10), .alu .and .rcx (.imm 1023),
     .alu .add .rcx (.imm 63), .alu .and .rcx (.imm (BitVec.ofInt 32 (-64))), .mov32 .rdi (.imm 0),
     .alu .cmp .rcx (.imm 961), .cmov .ae .rcx (.reg .rdi), .alu .cmp .r10 (.imm 961),
     .cmov .b .rcx (.reg .r10), .alu .cmp .r9 (.reg .rcx), .cmov .b .rcx (.reg .r9)]

/-- The copy's source and destination: `src` and `dst`. -/
def copyArgs : List Instr := [.mov .rsi (.reg .r8), .mov .rdi (.mem (at_ .rsp 8))]

/-- `key`, `nonce`, `aad_len` and `src` back from `work` (at `rax`); then
`work`, `tag` and `dst` into `r10`, `r11` and `rax`, for the frame. -/
def unstash : List Instr :=
  [.mov .rdi (.mem (at_ .rax 0)), .mov .rsi (.mem (at_ .rax 8)),
   .mov .rcx (.mem (at_ .rax 16)), .mov .r8 (.mem (at_ .rax 24)),
   .mov .r10 (.mem (at_ .rsp 32)), .mov .r11 (.mem (at_ .rsp 24)), .mov .rax (.mem (at_ .rsp 8))]

/-- The bytes of `src` to copy copied to `dst`, `w` bytes at a time, and the
values the frame pushes in registers. -/
def head (whole : Bool) (w : Width) : Prog isa :=
  .seq (.block loadW) (.seq (.block (stash ++ prefixLen whole ++ copyArgs))
  (.seq (copyBytes w) (.seq (.block loadW) (.block unstash))))

/-- `seal`'s data and its length into `r8` and `r9`: `dst`, and `len`, the
caller's second stack argument, above the frame. -/
def dataArgs : List Instr := [.mov .r8 (.reg .rax), .mov .r9 (.mem (at_ .rsp 56))]

/-- `body` in a frame laid out as `seal`'s entry: `dst` (where the return
address would be), `tag` and `work` (`seal`'s stack arguments), then `src`
and `src_len`. -/
def framed (body : Prog isa) : Prog isa :=
  .frame (.push [.r9, .r8, .r10, .r11, .rax]) (.seq (.block dataArgs) body) (.pop .rax 5)

/-- After `cryptArgsM` (the state, the data from byte `m`, its length and
`buf`), the arguments of `vg_chacha20_xor_split_avx512`: the state, `src`
from byte `k`, `src_len - k`, the data from byte `m`, its length and `buf`,
where `k` is the smaller of `m` (`rsi - r14`) and `src_len`. -/
def splitArgs : List Instr :=
  [.mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx), .mov .rcx (.reg .rsi), .mov .rax (.reg .rsi),
   .alu .sub .rax (.reg .r14), .mov .rdx (.mem (at_ .rsp 32)), .alu .cmp .rdx (.reg .rax),
   .cmov .b .rax (.reg .rdx), .mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rax),
   .alu .sub .rdx (.reg .rax)]

/-- As `cryptBig` with `vg_chacha20_xor_avx512`, but the call is replaced
by the code of `vg_chacha20_xor_split_avx512`, inline (its own call of
`vg_chacha20_xor_avx512` then takes the stack `seal`'s call took), with the
bytes of `src` after the first `m`; then `rsi` at `buf` (`ctx + 128`), as
`vg_chacha20_xor` leaves it. -/
def cryptBigSplit : Prog isa :=
  .seq (cryptPre 960 1024 6)
  (.seq (.block splitArgs)
  (.seq ChaCha20.X86_64.Avx512.xorSplit
    (.block (ptr .rsi .r15 128))))

/-- As `crypt` with `vg_chacha20_xor_avx512`, with `cryptBigSplit`. -/
def cryptSplit : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (960 + 1)))])
  (.seq (.ite .b
    (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX 6 .r14) (.block (ptr .rsi .r15 128))))
    cryptBigSplit)
  (.seq (.block (anchor .rsi 128))
  (.seq (foldM 960 1024)
  (.seq (.block [.alu .add .rdx (.imm 64)]) (zeroKs 6)))))

/-- The implementation `x` of `vg_chacha20_xor`, called as the AVX-512
instances call `vg_chacha20_xor_avx512` (`fold` 960, `pass` 1024, `wide` 6). -/
def bigCallee (x : ChaCha20.X86_64.Callee) : ChaCha20.X86_64.Callee :=
  { x with fold := 960, pass := 1024, wide := 6 }

/-- `seal` with the implementation `x` of `vg_chacha20_xor` for its prologue
(`vg_chacha20_xor_avx512` or `vg_chacha20_xor_avx512vl`) and `b` of
`vg_poly1305_blocks`, with `cryptSplit`. -/
def sealSplitBody (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue (bigCallee x))
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq cryptSplit
  (.seq (macPadLengths b .r14 .r13)
  (.seq finalizeTag
    (.block restore)))))))

/-- `vg_chacha20_poly1305_seal_split` of an instance, which calls the
implementation `x` of `vg_chacha20_xor` and `b` of `vg_poly1305_blocks`
(`vg_chacha20_xor_avx512` or `vg_chacha20_xor_avx512vl` for `.avx512` and
`.ifma`, whose `vg_chacha20_xor_split_avx512` calls `vg_chacha20_xor_avx512`). -/
def sealSplitFor (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => .seq (head false .z64) (framed (sealSplitBody x .avx512))
  | .ifma => .seq (head false .z64) (framed (sealSplitBody x .ifma))
  | b => .seq (head true (Width.ofBlocks b)) (framed (Stitch.sealFor x b))

end VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
