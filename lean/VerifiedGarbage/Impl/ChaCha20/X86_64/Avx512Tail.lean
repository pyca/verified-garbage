import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf

/-!
# ChaCha20 keystream XOR with AVX-512: the last bytes

`tail` XORs the last `rdx` bytes of data (fewer than 1024, at `rsi`) with the
keystream of the state at `rdi`, for `vg_chacha20_xor_avx512`, in at most
two computations of eight or four blocks:

* if at least 512 bytes remain, eight blocks (the counters `c, …, c + 7`
  modulo 2³², `c` being word 12 of the state) are XORed into the next 512
  bytes, and word 12 advanced by 8;
* then, if more than 256 bytes remain, eight blocks are computed: the first
  four XORed into the next 256 bytes, the other four stored to `buf[0, 256)`
  and as many of their bytes as remain XORed into the data
  (`XorBuf.xorBuf`);
* otherwise, if more than 64 bytes remain, four blocks are computed into
  `buf[0, 256)`, and as many of their bytes as remain XORed into the data;
  if fewer, but some, `vg_chacha20_xor` XORs them, one block costing less
  in general-purpose registers than four in `zmm` registers.

The states are kept one per 128-bit lane, four to a set of four `zmm`
registers (`zmm0 … zmm3`, and `zmm4 … zmm7` for the second four): row `r`
of the state of block `l` of a set in lane `l` of its `r`th register. Each
instruction of a quarter round then acts on the four columns (or, after
the rows are rotated with `vpshufd`, the four diagonals) of four blocks at
once, and every rotation is one `vprold`; the two sets' instructions are
interleaved. Each row of the state is broadcast to the four lanes with
`vbroadcasti32x4`; word 12 gets `0, 1, 2, 3` (or `4, 5, 6, 7`) added, lane
by lane, from `buf[256, 320)` (`buf[192, 256)`), written once by `consts`.
At the end, the input state is added again, and eight `vshufi32x4` gather
the lanes of a set's four registers into its four blocks.

`buf` is in `r9` throughout, which `xorBuf` keeps; `xorBuf` writes `rax`,
`r8` and `rcx`, and `vg_chacha20_xor` returns with `buf` in `rsi`. No
callee-saved register is written. The branches are on the length only,
and every address is a pointer plus a constant or a count, so only the
pointers and the length can affect timing.
-/

namespace VG.Impl.ChaCha20.X86_64.Avx512Tail

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- Where the lane increments of the first and the second set are in `buf`. -/
def incOff : Nat := 256
def inc2Off : Nat := 192

/-- `op zmm d, zmm a, zmm b`. -/
def z (op : ZBinOp) (d a b : XReg) : Instr := .zop (.zbin op d a b)

/-- The lane increments (in doubleword 0 of each 128-bit lane), as the
quadwords stored in `buf`. -/
def incQ : List (BitVec 64) := [0, 0, 1, 0, 2, 0, 3, 0]
def inc2Q : List (BitVec 64) := [4, 0, 5, 0, 6, 0, 7, 0]

/-- The lane increments into `buf` (at `rcx`). -/
def consts : List Instr := Avx2.storeQ incOff incQ ++ Avx2.storeQ inc2Off inc2Q

/-! ## Four blocks -/

/-- One half of the quarter round (RFC 8439 §2.1) on each of the four columns
of `a, b, c, d`, in each lane: `a += b; d ^= a; d <<<= r₁; c += d; b ^= c;
b <<<= r₂`. -/
def half (a b c d : XReg) (r₁ r₂ : BitVec 8) : List Instr :=
  [z .vpaddd a a b, z .vpxord d d a, .zop (.vprold d d r₁),
   z .vpaddd c c d, z .vpxord b b c, .zop (.vprold b b r₂)]

/-- Rotate rows `b, c, d` left by one, two and three words (`0x39, 0x4e,
0x93`), so that the columns are the diagonals, or back (`0x93, 0x4e,
0x39`). -/
def rot (b c d : XReg) (o₁ o₂ o₃ : BitVec 8) : List Instr :=
  [.zop (.vpshufd b b o₁), .zop (.vpshufd c c o₂), .zop (.vpshufd d d o₃)]

/-- `inner_block` (RFC 8439 §2.3.1) in each lane of `zmm0 … zmm3`: a column
round, then a diagonal round on the rotated rows. -/
def doubleRound : List Instr :=
  half .xmm0 .xmm1 .xmm2 .xmm3 16 12 ++ half .xmm0 .xmm1 .xmm2 .xmm3 8 7 ++
  rot .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++
  half .xmm0 .xmm1 .xmm2 .xmm3 16 12 ++ half .xmm0 .xmm1 .xmm2 .xmm3 8 7 ++
  rot .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block doubleRound)

/-- Rows 0–3 of the state (at `rdi`) broadcast into `zmm0 … zmm3`, with the
lane increments added to row 3 (through `zmm4`). -/
def setup : List Instr :=
  [.vbroadcasti32x4 .xmm0 (at_ .rdi 0), .vbroadcasti32x4 .xmm1 (at_ .rdi 16),
   .vbroadcasti32x4 .xmm2 (at_ .rdi 32), .vbroadcasti32x4 .xmm3 (at_ .rdi 48),
   .vmovdqu32Load .xmm4 (at_ .r9 incOff), z .vpaddd .xmm3 .xmm3 .xmm4]

/-- Gather the lanes of `a, b, c, d` (rows 0–3 of four blocks) into the four
blocks, in `a, b, c, d`, through `t0 … t3`. -/
def gather (a b c d t0 t1 t2 t3 : XReg) : List Instr :=
  [.zop (.vshufi32x4 t0 a b 0x44), .zop (.vshufi32x4 t1 c d 0x44),
   .zop (.vshufi32x4 t2 a b 0xee), .zop (.vshufi32x4 t3 c d 0xee),
   .zop (.vshufi32x4 a t0 t1 0x88), .zop (.vshufi32x4 b t0 t1 0xdd),
   .zop (.vshufi32x4 c t2 t3 0x88), .zop (.vshufi32x4 d t2 t3 0xdd)]

/-- The four blocks `a, b, c, d` into `buf[0, 256)`. -/
def store (a b c d : XReg) : List Instr :=
  [.vmovdqu32Store (at_ .r9 0) a, .vmovdqu32Store (at_ .r9 64) b,
   .vmovdqu32Store (at_ .r9 128) c, .vmovdqu32Store (at_ .r9 192) d]

/-- The rounds' result plus the input states (through `zmm4 … zmm8`), and the
four blocks gathered, into `buf[0, 256)`. -/
def finish : List Instr :=
  [.vbroadcasti32x4 .xmm4 (at_ .rdi 0), .vbroadcasti32x4 .xmm5 (at_ .rdi 16),
   .vbroadcasti32x4 .xmm6 (at_ .rdi 32), .vbroadcasti32x4 .xmm7 (at_ .rdi 48),
   .vmovdqu32Load .xmm8 (at_ .r9 incOff), z .vpaddd .xmm7 .xmm7 .xmm8,
   z .vpaddd .xmm0 .xmm0 .xmm4, z .vpaddd .xmm1 .xmm1 .xmm5,
   z .vpaddd .xmm2 .xmm2 .xmm6, z .vpaddd .xmm3 .xmm3 .xmm7] ++
  gather .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++ store .xmm0 .xmm1 .xmm2 .xmm3

/-! ## Eight blocks -/

/-- `half` on both sets, interleaved. -/
def half2 (r₁ r₂ : BitVec 8) : List Instr :=
  [z .vpaddd .xmm0 .xmm0 .xmm1, z .vpaddd .xmm4 .xmm4 .xmm5,
   z .vpxord .xmm3 .xmm3 .xmm0, z .vpxord .xmm7 .xmm7 .xmm4,
   .zop (.vprold .xmm3 .xmm3 r₁), .zop (.vprold .xmm7 .xmm7 r₁),
   z .vpaddd .xmm2 .xmm2 .xmm3, z .vpaddd .xmm6 .xmm6 .xmm7,
   z .vpxord .xmm1 .xmm1 .xmm2, z .vpxord .xmm5 .xmm5 .xmm6,
   .zop (.vprold .xmm1 .xmm1 r₂), .zop (.vprold .xmm5 .xmm5 r₂)]

/-- `rot` on both sets. -/
def rot2 (o₁ o₂ o₃ : BitVec 8) : List Instr :=
  rot .xmm1 .xmm2 .xmm3 o₁ o₂ o₃ ++ rot .xmm5 .xmm6 .xmm7 o₁ o₂ o₃

def doubleRound2 : List Instr :=
  half2 16 12 ++ half2 8 7 ++ rot2 0x39 0x4e 0x93 ++ half2 16 12 ++ half2 8 7 ++ rot2 0x93 0x4e 0x39

def rounds2 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds2 n) (.block doubleRound2)

/-- The rows into both sets, with their lane increments (through `zmm8`,
`zmm9`). -/
def setup2 : List Instr :=
  [.vbroadcasti32x4 .xmm0 (at_ .rdi 0), .vbroadcasti32x4 .xmm1 (at_ .rdi 16),
   .vbroadcasti32x4 .xmm2 (at_ .rdi 32), .vbroadcasti32x4 .xmm3 (at_ .rdi 48),
   z .vporq .xmm4 .xmm0 .xmm0, z .vporq .xmm5 .xmm1 .xmm1, z .vporq .xmm6 .xmm2 .xmm2,
   .vmovdqu32Load .xmm8 (at_ .r9 incOff), .vmovdqu32Load .xmm9 (at_ .r9 inc2Off),
   z .vpaddd .xmm7 .xmm3 .xmm9, z .vpaddd .xmm3 .xmm3 .xmm8]

/-- The rounds' result plus the input states (through `zmm8 … zmm13`), and
each set's blocks gathered (through `zmm8 … zmm11`). -/
def finish2 : List Instr :=
  [.vbroadcasti32x4 .xmm8 (at_ .rdi 0), .vbroadcasti32x4 .xmm9 (at_ .rdi 16),
   .vbroadcasti32x4 .xmm10 (at_ .rdi 32), .vbroadcasti32x4 .xmm11 (at_ .rdi 48),
   z .vpaddd .xmm0 .xmm0 .xmm8, z .vpaddd .xmm1 .xmm1 .xmm9, z .vpaddd .xmm2 .xmm2 .xmm10,
   z .vpaddd .xmm4 .xmm4 .xmm8, z .vpaddd .xmm5 .xmm5 .xmm9, z .vpaddd .xmm6 .xmm6 .xmm10,
   .vmovdqu32Load .xmm12 (at_ .r9 incOff), z .vpaddd .xmm12 .xmm12 .xmm11,
   z .vpaddd .xmm3 .xmm3 .xmm12,
   .vmovdqu32Load .xmm13 (at_ .r9 inc2Off), z .vpaddd .xmm13 .xmm13 .xmm11,
   z .vpaddd .xmm7 .xmm7 .xmm13] ++
  gather .xmm0 .xmm1 .xmm2 .xmm3 .xmm8 .xmm9 .xmm10 .xmm11 ++
  gather .xmm4 .xmm5 .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11

/-- XOR the 64 bytes in `x` into the data at `rsi + off`, through `zmm8`. -/
def xor64 (x : XReg) (off : Nat) : List Instr :=
  [.vmovdqu32Load .xmm8 (at_ .rsi off), z .vpxord .xmm8 .xmm8 x, .vmovdqu32Store (at_ .rsi off) .xmm8]

/-- The four blocks `a, b, c, d` XORed into the data at `rsi + off`. -/
def xor256 (a b c d : XReg) (off : Nat) : List Instr :=
  xor64 a off ++ xor64 b (off + 64) ++ xor64 c (off + 128) ++ xor64 d (off + 192)

/-! ## The tail -/

/-- XOR the `rdx` bytes of keystream in `buf` into the data. -/
def fromBuf : Prog isa := XorBuf.xorBuf .rsi .r9

/-- Eight blocks into the next 512 bytes of data; the counter, the data and
the length advanced. -/
def full : Prog isa :=
  .seq (.block setup2) (.seq (rounds2 10) (.block (finish2 ++
    xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256 ++
    [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
     .alu .add .rsi (.imm 512), .alu .sub .rdx (.imm 512)])))

/-- More than 256 bytes and fewer than 512: eight blocks, the first four into
the next 256 bytes of data, the others into `buf` and the rest of the data
from there. -/
def part : Prog isa :=
  .seq (.block setup2) (.seq (rounds2 10) (.seq (.block (finish2 ++
    xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7 ++
    [.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)])) fromBuf))

/-- At most 256 bytes: four blocks into `buf`, and the data from there. -/
def last : Prog isa :=
  .seq (.block setup) (.seq (rounds 10) (.seq (.block finish) fromBuf))

/-- The last `rdx` bytes, from 1 to 256. -/
def small : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 65)]) (.ite .b Avx2Tail.scalar last)

/-- The last `rdx` bytes (fewer than 1024); then `rsi` points at `buf`. -/
def tail : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 512)])
  (.seq (.ite .b (.block []) full)
  (.seq (.block [.alu .cmp .rdx (.imm 257)])
  (.seq (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) part)
    (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)]))))

end VG.Impl.ChaCha20.X86_64.Avx512Tail
