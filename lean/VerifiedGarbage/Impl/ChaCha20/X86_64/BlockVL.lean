module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2Tail

/-!
# The ChaCha20 block function on x86-64 with AVX-512VL, in `ymm` registers

`code` computes the block function of the 16-word state at `rdi` into the
first 64 bytes at `rsi`, as `vg_chacha20_block` does, for the streaming
`vg_chacha20_apply` of the implementations for CPUs with AVX-512VL to run
inline for the last bytes in place of calling it: with each rotation one
`vprold`, the rows of one state in `ymm0 … ymm3` (`Avx2Tail.roundsS true 1`)
take less time than the scalar code's four columns at once.

Each row is broadcast to both lanes, so both compute the block; the rounds'
result plus the input state is written, both lanes, to the 128 bytes at
`rsi` (through `r9`, as `Avx2Tail.storeSet` writes), and the upper halves of
the registers are cleared. It writes `r9`, `ymm0 … ymm3` and `ymm10`, and
reads no address but `rdi` and `rsi` plus constants: only the pointers can
affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.BlockVL

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20.X86_64.Avx2Tail (v roundsS storeSet)

/-- The rows of the state into both lanes of `ymm0 … ymm3`. -/
def setup : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), .vbroadcasti128 .xmm1 (at_ .rdi 16),
   .vbroadcasti128 .xmm2 (at_ .rdi 32), .vbroadcasti128 .xmm3 (at_ .rdi 48)]

/-- The rounds' result plus the input state (through `ymm10`), and the two
lanes' blocks to the 128 bytes at `r9`. -/
def finish : List Instr :=
  ([.vbroadcasti128 .xmm10 (at_ .rdi 0), v .vpaddd .xmm0 .xmm0 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 16), v .vpaddd .xmm1 .xmm1 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 32), v .vpaddd .xmm2 .xmm2 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 48), v .vpaddd .xmm3 .xmm3 .xmm10] : List Instr) ++
  storeSet .xmm0 .xmm1 .xmm2 .xmm3 0

/-- The output's address into `r9`, the block, and the upper halves of the
registers cleared. -/
def code : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rsi)]) (.seq (.block setup) (.seq (roundsS true 1 10)
    (.seq (.block finish) (.block [.vop .vzeroupper]))))

end VG.Impl.ChaCha20.X86_64.BlockVL
