import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512To

/-!
# ChaCha20-Poly1305 encryption with part of the data read from elsewhere: x86-64

`sealTo b` is `seal` (`../X86_64.lean`) with the implementation of
`vg_chacha20_xor` for AVX-512 (`Callee.avx512`), run inline by
`vg_chacha20_poly1305_seal_gather` with two more stack arguments: `src` at
`[rsp + 24]` and `src_len` at `[rsp + 32]`, the first of the slices it
gathers. Where `seal`'s second call of `vg_chacha20_xor` would encrypt the
data from byte `m` (`foldM`) on, `sealTo` first encrypts the whole 1024-byte
passes of `src` from its byte `m` on, `P` bytes (none if `src_len ≤ m`),
reading them from `src` and writing them to the data (`oop`: the loop of
`vg_chacha20_xor_to_avx512`, `xorToLoop`, inline), with a copy of the
ChaCha20 state in `ctx[608, 672)`; then the call encrypts the data after
byte `m + P` in place. So the data's bytes `[m, m + P)` need not have been
copied from `src` before.

`rbx`, which holds the additional data only until the lengths block is
stored, keeps `m + P` across the loop.
-/

namespace VG.Impl.ChaCha20Poly1305.X86_64

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- The loop of `vg_chacha20_xor_to_avx512`: its whole 1024-byte passes. -/
def xorToLoop : Prog isa :=
  .seq (.block (ChaCha20.X86_64.Avx512.entryTo ++ ChaCha20.X86_64.Avx512.consts ++
    ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
  (.ite .b (.block []) (.loop ChaCha20.X86_64.Avx512.bodyTo .ae))

/-- With `m` in `rbx` and `P` in `rax`: the loop's arguments (the copy of the
state, whose counter is already `1 + m / 64`, `src + m`, `P`, the data from
byte `m`, and `buf`), and `m + P` in `rbx`. -/
def oopArgs : List Instr :=
  [.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0,
   .mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx),
   .mov .rcx (.reg .r14), .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] ++
  ptr .rdi .r15 608 ++ ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr)

/-- As `cryptArgsM`, after the first `rbx` bytes. -/
def restArgs : List Instr :=
  [.mov .rax (.reg .rbx), .shift .shr .rax 6, .alu .add .rax (.imm 1), .store32 (at_ .r15 112) .rax,
   .mov .rsi (.reg .r14), .alu .add .rsi (.reg .rbx), .mov .rdx (.reg .r13), .alu .sub .rdx (.reg .rbx)] ++
  ptr .rdi .r15 64 ++ ptr .rcx .r15 128

/-- After `cryptPre` (`m` is `r13 - rdx`): if `src_len > m`, the `P` bytes
of `src` from byte `m` on, `src_len - m` rounded down to a multiple of 1024,
if any, encrypted into the data, and the arguments of the call for the rest. -/
def oop : Prog isa :=
  .seq (.block [.mov .rbx (.reg .r13), .alu .sub .rbx (.reg .rdx), .mov .rax (.mem (at_ .rsp 32)),
    .alu .cmp .rax (.reg .rbx)])
  (.ite .b (.block [])
    (.seq (.block [.alu .sub .rax (.reg .rbx), .shift .shr .rax 10, .shift .shl .rax 10,
        .alu .test .rax (.reg .rax)])
      (.ite .e (.block [])
        (.seq (.block oopArgs) (.seq xorToLoop (.block restArgs))))))

/-- As `cryptBig`, with `oop` before the call. -/
def cryptBigTo (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (cryptPre x.fold x.pass x.wide) (.seq oop (.call x.name x.code))

/-- As `crypt`, with `cryptBigTo`. -/
def cryptTo (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))])
  (.seq (.ite .b
    (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX x.wide .r14) (.block (ptr .rsi .r15 128))))
    (cryptBigTo x))
  (.seq (.block (anchor .rsi 128))
  (.seq (foldM x.fold x.pass)
  (.seq (.block [.alu .add .rdx (.imm 64)]) (zeroKs x.wide)))))

/-- `seal` for AVX-512, with `cryptTo`. -/
def sealTo (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue ChaCha20.X86_64.Callee.avx512)
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq (cryptTo ChaCha20.X86_64.Callee.avx512)
  (.seq (macPadLengths b .r14 .r13)
  (.seq finalizeTag
    (.block restore)))))))

end VG.Impl.ChaCha20Poly1305.X86_64
