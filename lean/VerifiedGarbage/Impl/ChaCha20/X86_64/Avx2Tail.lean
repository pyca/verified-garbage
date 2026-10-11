module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
public import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf

/-!
# ChaCha20 keystream XOR with AVX2: the last bytes

`tail` XORs the last `rdx` bytes of data (fewer than 385, at `rsi`) with the
keystream of the state at `rdi`, for `vg_chacha20_xor_avx2`, in one
computation of up to six blocks (the counters `c, c + 1, …` modulo 2³², `c`
being word 12 of the state):

* if more than 256 bytes remain, six blocks (`last3`): the first four
  XORed into the next 256 bytes, the last two computed into `buf[0, 128)`;
  as many of their bytes as remain are XORed into the data
  (`XorBuf.xorBuf`);
* if 129 to 256, four blocks are computed into `buf[0, 256)`, and the data
  XORed from there; if 65 to 128, two blocks into `buf[0, 128)`, the same;
  if fewer, but some, `vg_chacha20_xor` XORs them (`scalar`).

The rounds of a computation take about the same time for two, four or six
blocks (they are bound by the latency of a quarter round, not by its
throughput), so it computes as many blocks as remain.

The states are kept one per 128-bit lane, two to a set of four `ymm`
registers (`ymm0 … ymm3`, and `ymm4 … ymm7` for the second two): row `r` of
the state of block `l` of a set in lane `l` of its `r`th register. Each
instruction of a quarter round then acts on the four columns (or, after the
rows are rotated with `vpshufd`, the four diagonals) of two blocks at once;
the two sets' instructions are interleaved. A rotation by 16 or 8 is a
`vpshufb` with the masks `vg_chacha20_xor_avx2` keeps in `buf[128, 192)`
(loaded into `ymm8`, `ymm9`); one by 12 or 7 is two shifts and a `vpor`
(through `ymm10`, `ymm11`). Each row of the state is broadcast to both lanes
with `vbroadcasti128`; word 12 gets `0, 1` (or `2, 3`) added, lane by lane,
from `buf[224, 288)` (into `ymm12`, `ymm13`), written once by `consts`. At
the end, the input state is added again (the increments loaded again), and
`vperm2i128` gathers the lanes of a set's four registers into its two blocks.

`buf` is in `r9` throughout, which `xorBuf` keeps; `xorBuf` writes `rax`,
`r8` and `rcx`, and `vg_chacha20_xor` returns with `buf` in `rsi`. No
callee-saved register is written. The branches are on the length only,
and every address is a pointer plus a constant or a count, so only the
pointers and the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.Avx2Tail

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
/-- `op dst, a, b` on 256 bits. -/
def v (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- Where `vg_chacha20_xor_avx2` keeps the masks of the rotations by 16 and 8
in `buf` (`Avx2.rot16Off`, `Avx2.rot8Off`). -/
def rot16Off : Nat := 128
def rot8Off : Nat := 160

/-- Store the quadwords `qs` at `buf + off` (`buf` in `rcx`), through `rax`. -/
def storeQ (off : Nat) (qs : List (BitVec 64)) : List Instr :=
  (List.range qs.length).flatMap fun i =>
    [.movImm64 .rax (qs.getD i 0), .store (at_ .rcx (off + 8 * i)) .rax]

/-- Where the lane increments of the first and the second set are in `buf`. -/
def incOff : Nat := 224
def inc2Off : Nat := 256

/-- The lane increments (in doubleword 0 of each 128-bit lane), as the
quadwords stored in `buf`. -/
def incQ : List (BitVec 64) := [0, 0, 1, 0]
def inc2Q : List (BitVec 64) := [2, 0, 3, 0]

/-- The lane increments into `buf` (at `rcx`). -/
def consts : List Instr := storeQ incOff incQ ++ storeQ inc2Off inc2Q

/-- A rotation left by 16 (`ymm8`) or 8 (`ymm9`) of the doublewords of `d`. -/
def rotB (d m : XReg) : List Instr := [v .vpshufb d d m]

/-- A rotation left by `n` of the doublewords of `d`, through `t`. -/
def rotS (d t : XReg) (n : Nat) : List Instr :=
  [.vop (.vshift .pslld .l256 t d (BitVec.ofNat 8 n)), .vop (.vshift .psrld .l256 d d (BitVec.ofNat 8 (32 - n))),
   v .vpor d d t]

/-- One half of the quarter round (RFC 8439 §2.1) on each of the four columns
of both sets, interleaved: `a += b; d ^= a; d <<<= r₁; c += d; b ^= c;
b <<<= r₂`, the rotation of `d` by `vpshufb` with `m` and that of `b` by `n`. -/
def half2 (m : XReg) (n : Nat) : List Instr :=
  [v .vpaddd .xmm0 .xmm0 .xmm1, v .vpaddd .xmm4 .xmm4 .xmm5,
   v .vpxor .xmm3 .xmm3 .xmm0, v .vpxor .xmm7 .xmm7 .xmm4] ++
  rotB .xmm3 m ++ rotB .xmm7 m ++
  [v .vpaddd .xmm2 .xmm2 .xmm3, v .vpaddd .xmm6 .xmm6 .xmm7,
   v .vpxor .xmm1 .xmm1 .xmm2, v .vpxor .xmm5 .xmm5 .xmm6] ++
  rotS .xmm1 .xmm10 n ++ rotS .xmm5 .xmm11 n

/-- Rotate rows `b, c, d` of both sets left by one, two and three words
(`0x39, 0x4e, 0x93`), or back (`0x93, 0x4e, 0x39`). -/
def rot2 (o₁ o₂ o₃ : BitVec 8) : List Instr :=
  [.vop (.vpshufd .l256 .xmm1 .xmm1 o₁), .vop (.vpshufd .l256 .xmm2 .xmm2 o₂),
   .vop (.vpshufd .l256 .xmm3 .xmm3 o₃), .vop (.vpshufd .l256 .xmm5 .xmm5 o₁),
   .vop (.vpshufd .l256 .xmm6 .xmm6 o₂), .vop (.vpshufd .l256 .xmm7 .xmm7 o₃)]

/-- `inner_block` (RFC 8439 §2.3.1) in each lane of both sets. -/
def doubleRound2 : List Instr :=
  half2 .xmm8 12 ++ half2 .xmm9 7 ++ rot2 0x39 0x4e 0x93 ++
  half2 .xmm8 12 ++ half2 .xmm9 7 ++ rot2 0x93 0x4e 0x39

def rounds2 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds2 n) (.block doubleRound2)

/-- `half2` on the first set only. -/
def half1 (m : XReg) (n : Nat) : List Instr :=
  [v .vpaddd .xmm0 .xmm0 .xmm1, v .vpxor .xmm3 .xmm3 .xmm0] ++ rotB .xmm3 m ++
  [v .vpaddd .xmm2 .xmm2 .xmm3, v .vpxor .xmm1 .xmm1 .xmm2] ++ rotS .xmm1 .xmm10 n

def rot1 (o₁ o₂ o₃ : BitVec 8) : List Instr :=
  [.vop (.vpshufd .l256 .xmm1 .xmm1 o₁), .vop (.vpshufd .l256 .xmm2 .xmm2 o₂),
   .vop (.vpshufd .l256 .xmm3 .xmm3 o₃)]

def doubleRound1 : List Instr :=
  half1 .xmm8 12 ++ half1 .xmm9 7 ++ rot1 0x39 0x4e 0x93 ++
  half1 .xmm8 12 ++ half1 .xmm9 7 ++ rot1 0x93 0x4e 0x39

def rounds1 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds1 n) (.block doubleRound1)

/-- The rows into the first set, with its lane increments, and the masks. -/
def setup1 : List Instr :=
  [.vmovdquLoad .l256 .xmm8 (at_ .r9 rot16Off), .vmovdquLoad .l256 .xmm9 (at_ .r9 rot8Off),
   .vmovdquLoad .l256 .xmm12 (at_ .r9 incOff),
   .vbroadcasti128 .xmm0 (at_ .rdi 0), .vbroadcasti128 .xmm1 (at_ .rdi 16),
   .vbroadcasti128 .xmm2 (at_ .rdi 32), .vbroadcasti128 .xmm3 (at_ .rdi 48),
   v .vpaddd .xmm3 .xmm3 .xmm12]

def addIn1 : List Instr :=
  [.vmovdquLoad .l256 .xmm12 (at_ .r9 incOff),
   .vbroadcasti128 .xmm10 (at_ .rdi 0), v .vpaddd .xmm0 .xmm0 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 16), v .vpaddd .xmm1 .xmm1 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 32), v .vpaddd .xmm2 .xmm2 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 48), v .vpaddd .xmm11 .xmm10 .xmm12, v .vpaddd .xmm3 .xmm3 .xmm11]

/-- The rows into both sets, with their lane increments, and the masks. -/
def setup : List Instr :=
  [.vmovdquLoad .l256 .xmm8 (at_ .r9 rot16Off), .vmovdquLoad .l256 .xmm9 (at_ .r9 rot8Off),
   .vmovdquLoad .l256 .xmm12 (at_ .r9 incOff), .vmovdquLoad .l256 .xmm13 (at_ .r9 inc2Off),
   .vbroadcasti128 .xmm0 (at_ .rdi 0), .vbroadcasti128 .xmm1 (at_ .rdi 16),
   .vbroadcasti128 .xmm2 (at_ .rdi 32), .vbroadcasti128 .xmm3 (at_ .rdi 48),
   v .vpor .xmm4 .xmm0 .xmm0, v .vpor .xmm5 .xmm1 .xmm1, v .vpor .xmm6 .xmm2 .xmm2,
   v .vpaddd .xmm7 .xmm3 .xmm13, v .vpaddd .xmm3 .xmm3 .xmm12]

/-- The rounds' result plus the input states (through `ymm10 … ymm13`). -/
def addIn : List Instr :=
  [.vmovdquLoad .l256 .xmm12 (at_ .r9 incOff), .vmovdquLoad .l256 .xmm13 (at_ .r9 inc2Off),
   .vbroadcasti128 .xmm10 (at_ .rdi 0), v .vpaddd .xmm0 .xmm0 .xmm10, v .vpaddd .xmm4 .xmm4 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 16), v .vpaddd .xmm1 .xmm1 .xmm10, v .vpaddd .xmm5 .xmm5 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 32), v .vpaddd .xmm2 .xmm2 .xmm10, v .vpaddd .xmm6 .xmm6 .xmm10,
   .vbroadcasti128 .xmm10 (at_ .rdi 48), v .vpaddd .xmm11 .xmm10 .xmm12, v .vpaddd .xmm3 .xmm3 .xmm11,
   v .vpaddd .xmm11 .xmm10 .xmm13, v .vpaddd .xmm7 .xmm7 .xmm11]

/-- The two blocks of the set `a, b, c, d`, gathered through `ymm10` and
stored to `buf + off`. -/
def storeSet (a b c d : XReg) (off : Nat) : List Instr :=
  [.vop (.vperm2i128 .xmm10 a b 0x20), .vmovdquStore .l256 (at_ .r9 off) .xmm10,
   .vop (.vperm2i128 .xmm10 c d 0x20), .vmovdquStore .l256 (at_ .r9 (off + 32)) .xmm10,
   .vop (.vperm2i128 .xmm10 a b 0x31), .vmovdquStore .l256 (at_ .r9 (off + 64)) .xmm10,
   .vop (.vperm2i128 .xmm10 c d 0x31), .vmovdquStore .l256 (at_ .r9 (off + 96)) .xmm10]

/-! ## Three sets

Six blocks at once, for 257 to 384 bytes: a third set in `ymm8 … ymm11`,
the masks in `ymm14`, `ymm15` and the rotations' scratch in `ymm12`,
`ymm13`. The third set's lane increments, `4, 5`, are the second set's
`2, 3` plus their low lane in both lanes (`vperm2i128`), so `buf` holds no
more constants. -/

/-- `half2` on three sets, the third in `ymm8 … ymm11`, the masks in
`ymm14`, `ymm15`, and the rotations by shifts through `ymm12`, `ymm13`. -/
def half3 (m : XReg) (n : Nat) : List Instr :=
  [v .vpaddd .xmm0 .xmm0 .xmm1, v .vpaddd .xmm4 .xmm4 .xmm5, v .vpaddd .xmm8 .xmm8 .xmm9,
   v .vpxor .xmm3 .xmm3 .xmm0, v .vpxor .xmm7 .xmm7 .xmm4, v .vpxor .xmm11 .xmm11 .xmm8] ++
  rotB .xmm3 m ++ rotB .xmm7 m ++ rotB .xmm11 m ++
  [v .vpaddd .xmm2 .xmm2 .xmm3, v .vpaddd .xmm6 .xmm6 .xmm7, v .vpaddd .xmm10 .xmm10 .xmm11,
   v .vpxor .xmm1 .xmm1 .xmm2, v .vpxor .xmm5 .xmm5 .xmm6, v .vpxor .xmm9 .xmm9 .xmm10] ++
  rotS .xmm1 .xmm12 n ++ rotS .xmm5 .xmm13 n ++ rotS .xmm9 .xmm12 n

def rot3 (o₁ o₂ o₃ : BitVec 8) : List Instr :=
  rot2 o₁ o₂ o₃ ++
  [.vop (.vpshufd .l256 .xmm9 .xmm9 o₁), .vop (.vpshufd .l256 .xmm10 .xmm10 o₂),
   .vop (.vpshufd .l256 .xmm11 .xmm11 o₃)]

def doubleRound3 : List Instr :=
  half3 .xmm14 12 ++ half3 .xmm15 7 ++ rot3 0x39 0x4e 0x93 ++
  half3 .xmm14 12 ++ half3 .xmm15 7 ++ rot3 0x93 0x4e 0x39

def rounds3 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds3 n) (.block doubleRound3)

/-- The rows into the three sets, with their lane increments, and the masks. -/
def setup3 : List Instr :=
  [.vmovdquLoad .l256 .xmm14 (at_ .r9 rot16Off), .vmovdquLoad .l256 .xmm15 (at_ .r9 rot8Off),
   .vmovdquLoad .l256 .xmm12 (at_ .r9 incOff), .vmovdquLoad .l256 .xmm13 (at_ .r9 inc2Off),
   .vbroadcasti128 .xmm0 (at_ .rdi 0), .vbroadcasti128 .xmm1 (at_ .rdi 16),
   .vbroadcasti128 .xmm2 (at_ .rdi 32), .vbroadcasti128 .xmm3 (at_ .rdi 48),
   v .vpor .xmm4 .xmm0 .xmm0, v .vpor .xmm5 .xmm1 .xmm1, v .vpor .xmm6 .xmm2 .xmm2,
   v .vpor .xmm8 .xmm0 .xmm0, v .vpor .xmm9 .xmm1 .xmm1, v .vpor .xmm10 .xmm2 .xmm2,
   .vop (.vperm2i128 .xmm11 .xmm13 .xmm13 0x00), v .vpaddd .xmm11 .xmm11 .xmm13,
   v .vpaddd .xmm11 .xmm11 .xmm3,
   v .vpaddd .xmm7 .xmm3 .xmm13, v .vpaddd .xmm3 .xmm3 .xmm12]

/-- The rounds' result plus the input states (through `ymm12 … ymm15`). -/
def addIn3 : List Instr :=
  [.vbroadcasti128 .xmm14 (at_ .rdi 0), v .vpaddd .xmm0 .xmm0 .xmm14, v .vpaddd .xmm4 .xmm4 .xmm14,
   v .vpaddd .xmm8 .xmm8 .xmm14,
   .vbroadcasti128 .xmm14 (at_ .rdi 16), v .vpaddd .xmm1 .xmm1 .xmm14, v .vpaddd .xmm5 .xmm5 .xmm14,
   v .vpaddd .xmm9 .xmm9 .xmm14,
   .vbroadcasti128 .xmm14 (at_ .rdi 32), v .vpaddd .xmm2 .xmm2 .xmm14, v .vpaddd .xmm6 .xmm6 .xmm14,
   v .vpaddd .xmm10 .xmm10 .xmm14,
   .vmovdquLoad .l256 .xmm12 (at_ .r9 incOff), .vmovdquLoad .l256 .xmm13 (at_ .r9 inc2Off),
   .vbroadcasti128 .xmm14 (at_ .rdi 48),
   v .vpaddd .xmm15 .xmm14 .xmm12, v .vpaddd .xmm3 .xmm3 .xmm15,
   v .vpaddd .xmm15 .xmm14 .xmm13, v .vpaddd .xmm7 .xmm7 .xmm15,
   .vop (.vperm2i128 .xmm15 .xmm13 .xmm13 0x00), v .vpaddd .xmm15 .xmm15 .xmm13,
   v .vpaddd .xmm15 .xmm15 .xmm14, v .vpaddd .xmm11 .xmm11 .xmm15]

/-- XOR the 32 bytes in `x` into the data at `rsi + off`, through `t`. -/
def xor32T (t x : XReg) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 t (at_ .rsi off), v .vpxor t t x, .vmovdquStore .l256 (at_ .rsi off) t]

/-- The two blocks of the set `a, b, c, d`, gathered through `ymm12` and
XORed into the data at `rsi + off`, through `ymm13`. -/
def xorSetT (a b c d : XReg) (off : Nat) : List Instr :=
  [.vop (.vperm2i128 .xmm12 a b 0x20)] ++ xor32T .xmm13 .xmm12 off ++
  [.vop (.vperm2i128 .xmm12 c d 0x20)] ++ xor32T .xmm13 .xmm12 (off + 32) ++
  [.vop (.vperm2i128 .xmm12 a b 0x31)] ++ xor32T .xmm13 .xmm12 (off + 64) ++
  [.vop (.vperm2i128 .xmm12 c d 0x31)] ++ xor32T .xmm13 .xmm12 (off + 96)

/-- `storeSet`, through `ymm12`. -/
def storeSetT (a b c d : XReg) (off : Nat) : List Instr :=
  [.vop (.vperm2i128 .xmm12 a b 0x20), .vmovdquStore .l256 (at_ .r9 off) .xmm12,
   .vop (.vperm2i128 .xmm12 c d 0x20), .vmovdquStore .l256 (at_ .r9 (off + 32)) .xmm12,
   .vop (.vperm2i128 .xmm12 a b 0x31), .vmovdquStore .l256 (at_ .r9 (off + 64)) .xmm12,
   .vop (.vperm2i128 .xmm12 c d 0x31), .vmovdquStore .l256 (at_ .r9 (off + 96)) .xmm12]

/-! ## The tail -/

/-- XOR the `rdx` bytes of keystream in `buf` into the data. -/
def fromBuf : Prog isa := XorBuf.xorBuf .rsi .r9

/-- At most 256 bytes: four blocks into `buf`, and the data from there. -/
def last : Prog isa :=
  .seq (.block setup) (.seq (rounds2 10) (.seq (.block (addIn ++
    storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128)) fromBuf))

/-- At most 128 bytes: two blocks into `buf`, and the data from there. -/
def last1 : Prog isa :=
  .seq (.block setup1) (.seq (rounds1 10) (.seq (.block (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0))
    fromBuf))

/-- At most 64 bytes, by `vg_chacha20_xor`, whose one block takes less time
than several in vector registers (here and in `vg_chacha20_xor_avx512`); it
returns with `rsi` pointing at `buf`, which goes back to `r9`. -/
def scalar : Prog isa :=
  .seq (.block [.vop .vzeroupper]) (.seq (.call "vg_chacha20_xor" Xor.xor) (.block [.mov .r9 (.reg .rsi)]))

/-- The last `rdx` bytes, from 1 to 128. -/
def small : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 65)]) (.ite .b scalar last1)

/-- 257 to 384 bytes: six blocks, the first four XORed into the next 256
bytes of data and the last two into `buf`, from which the rest is XORed. -/
def last3 : Prog isa :=
  .seq (.block setup3) (.seq (rounds3 10) (.seq (.block (addIn3 ++
    xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
    storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0 ++
    ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) fromBuf))

/-- Fewer than 257 bytes. -/
def rest : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 129)])
    (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) last)

/-- The last `rdx` bytes (fewer than 385); then `rsi` points at `buf`. -/
def tail : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 257)])
  (.seq (.ite .b rest last3)
    (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)]))

end VG.Impl.ChaCha20.X86_64.Avx2Tail
