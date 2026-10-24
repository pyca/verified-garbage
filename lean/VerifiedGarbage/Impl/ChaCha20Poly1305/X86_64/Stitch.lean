module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305: x86-64, with Poly1305 inside the AVX2 ChaCha20 kernel

`seal` (`../X86_64.lean`) encrypts the data with one call of
`vg_chacha20_xor` and then absorbs the ciphertext with calls of
`vg_poly1305_blocks`. The AVX2 kernel (`Impl/ChaCha20/X86_64/Avx2.lean`)
keeps the vector units busy and leaves the integer units, the multiplier and
twelve general-purpose registers idle: `sealStitched` fills them with the
scalar Poly1305 (`Impl/Poly1305/X86_64.lean`), as BoringSSL's
`chacha20_poly1305_x86_64.pl` does with its own kernel. The two
computations are independent, so out-of-order cores overlap them.

With at least 512 bytes of data, `bulk` encrypts its whole chunks of 512
bytes: the first with the kernel's code (`firstChunk`), and each later one
with the kernel's code in which every double round absorbs three or four
blocks of Poly1305 (`chunk`): the 32 blocks of the chunk before it, whose
ciphertext is complete. Each block is absorbed in two pieces, the block
added and its products (`addProd`), then their carry, each after one of the
round's quarter rounds (`sround4`, `sround3`): a whole double round of
vector code and then three or four blocks of scalar code would each leave
the other's units idle for longer than the out-of-order window can cover.
`rsi` points at that chunk while the rounds run, and is advanced to the
chunk being encrypted just before the kernel's `finish` XORs the keystream
into it.

Every register but `rsp` is busy during a chunk: `rdi`, `rsi` and `rcx` are
the kernel's (the ChaCha20 state, the data and `buf`), and the other twelve
are Poly1305's (`r8`–`r10` for the key, `r11`, `rbx`, `rbp` for the
accumulator, the rest for the products). So the number of bytes left lives
in the Poly1305 state's working space (`lenOff`), which `vg_poly1305_blocks`
uses only while it runs, and `r12`–`r14` (`tag`, the length and the data,
which `seal` needs afterwards) are stashed there by `enter`. If 1 to 256
bytes are left after the whole chunks, `tailS` encrypts them while it
absorbs the last chunk (see below), and leaves `rdx` 0. Otherwise `leave`
reduces the accumulator, stores it, restores the registers, and leaves in
`rbx`, `rbp` the ciphertext not yet absorbed (the last chunk and the rest),
and in `rsi`, `rdx` the data not yet encrypted, for the call of
`vg_chacha20_xor` that follows if `rdx` is not 0. The branches are on the
length only.

When whole chunks and 1 to 64 bytes would be left after the first 448 bytes
(the length 448 to 511 bytes past a multiple of 512, or a multiple of 512), or
the data is shorter than 1409 bytes, `sealFor` has the prologue compute the
keystream of those 448 bytes with the one-time key's block (`splitM` for
`pass` 512: eight blocks, one pass of the kernel), and `preS` encrypts them
with it (`cryptPre`). Then the first chunk absorbs them (`chunk true`, whose
rounds absorb 28 blocks), and `restT` absorbs the last chunk while it
encrypts the bytes after it; or, with no whole chunk, `tailP` absorbs the 448
bytes while it encrypts the 1 to 512 after them, by `tailS` or `tailK`'s
code. Either way only those last bytes are left for `macPadLengths` to
absorb.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.X86_64.Stitch

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)

/-- Offsets in `buf` (`ctx + 128`), in the Poly1305 state's working space
(`ctx + 520 …`): `r12`, `r13`, `r14` stashed, and the bytes left. -/
def r12Off : Nat := 392
def r13Off : Nat := 400
def r14Off : Nat := 408
def lenOff : Nat := 416

/-- The accumulator's offset in `buf`: the Poly1305 state at `ctx + 448`. -/
def accOff : Nat := 320

/-- The blocks a chunk's rounds absorb: the 32 of the chunk before it, or
(`pre`) the 28 of the 448 bytes before the first chunk. -/
def total (pre : Bool) : Nat := if pre then 28 else 32

/-- After double round `n` of a chunk, `blocks pre n` blocks are absorbed,
from block `firstBlock pre n`: of 32, four after the first two and three after
the others; of 28 (`pre`), four after the first, three after the next eight
and none after the last. -/
def blocks (pre : Bool) (n : Nat) : Nat :=
  if pre then (if n = 0 then 4 else if n < 9 then 3 else 0) else if n < 2 then 4 else 3
def firstBlock (pre : Bool) (n : Nat) : Nat :=
  if pre then (if n = 0 then 0 else min (3 * n + 1) 28) else if n < 2 then 4 * n else 3 * n + 2

/-- The first piece of block `j` of the 512 bytes at `rsi`: the block added
to the accumulator, and the products of the sum. Its second piece is
`Poly1305.X86_64.carryS`. -/
def addProd (j : Nat) : List Instr :=
  Poly1305.X86_64.addBlockAt .rsi (16 * j) 1 ++ Poly1305.X86_64.productsS

section
open ChaCha20.X86_64.Avx2 (quarter swap)

/-- A double round (`Avx2.doubleRound`) absorbing blocks `j` to `j + 3`, a
piece after each quarter round. -/
def sround4 (j : Nat) : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (.block (addProd j)) <|
  .seq (quarter 1 5 9 13) <| .seq (.block Poly1305.X86_64.carryS) <| .seq (swap 8 10) <|
  .seq (quarter 2 6 10 14) <| .seq (.block (addProd (j + 1))) <|
  .seq (quarter 3 7 11 15) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarter 0 5 10 15) <| .seq (.block (addProd (j + 2))) <|
  .seq (quarter 1 6 11 12) <| .seq (.block Poly1305.X86_64.carryS) <| .seq (swap 10 8) <|
  .seq (quarter 2 7 8 13) <| .seq (.block (addProd (j + 3))) <|
  .seq (quarter 3 4 9 14) (.block Poly1305.X86_64.carryS)

/-- A double round absorbing blocks `j` to `j + 2`: a piece after each
quarter round but the first of each half. -/
def sround3 (j : Nat) : Prog isa :=
  .seq (quarter 0 4 8 12) <|
  .seq (quarter 1 5 9 13) <| .seq (.block (addProd j)) <| .seq (swap 8 10) <|
  .seq (quarter 2 6 10 14) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarter 3 7 11 15) <| .seq (.block (addProd (j + 1))) <|
  .seq (quarter 0 5 10 15) <|
  .seq (quarter 1 6 11 12) <| .seq (.block Poly1305.X86_64.carryS) <| .seq (swap 10 8) <|
  .seq (quarter 2 7 8 13) <| .seq (.block (addProd (j + 2))) <|
  .seq (quarter 3 4 9 14) (.block Poly1305.X86_64.carryS)

end

/-- Double round `n`, absorbing its blocks. -/
def sround (pre : Bool) (n : Nat) : Prog isa :=
  if blocks pre n = 4 then sround4 (firstBlock pre n)
  else if blocks pre n = 3 then sround3 (firstBlock pre n)
  else ChaCha20.X86_64.Avx2.doubleRound

/-- `n` double rounds, each absorbing its blocks. -/
def srounds (pre : Bool) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (srounds pre n) (sround pre n)

section
open ChaCha20.X86_64.Avx2 (quarterV)

/-- `sround4` with `vprold` (`Avx2.doubleRoundV`): every word in its register,
nothing swapped. -/
def sround4V (j : Nat) : Prog isa :=
  .seq (quarterV 0 4 8 12) <| .seq (.block (addProd j)) <|
  .seq (quarterV 1 5 9 13) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarterV 2 6 10 14) <| .seq (.block (addProd (j + 1))) <|
  .seq (quarterV 3 7 11 15) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarterV 0 5 10 15) <| .seq (.block (addProd (j + 2))) <|
  .seq (quarterV 1 6 11 12) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarterV 2 7 8 13) <| .seq (.block (addProd (j + 3))) <|
  .seq (quarterV 3 4 9 14) (.block Poly1305.X86_64.carryS)

/-- `sround3` with `vprold`. -/
def sround3V (j : Nat) : Prog isa :=
  .seq (quarterV 0 4 8 12) <|
  .seq (quarterV 1 5 9 13) <| .seq (.block (addProd j)) <|
  .seq (quarterV 2 6 10 14) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarterV 3 7 11 15) <| .seq (.block (addProd (j + 1))) <|
  .seq (quarterV 0 5 10 15) <|
  .seq (quarterV 1 6 11 12) <| .seq (.block Poly1305.X86_64.carryS) <|
  .seq (quarterV 2 7 8 13) <| .seq (.block (addProd (j + 2))) <|
  .seq (quarterV 3 4 9 14) (.block Poly1305.X86_64.carryS)

end

/-- `sround` with `vprold`. -/
def sroundV (pre : Bool) (n : Nat) : Prog isa :=
  if blocks pre n = 4 then sround4V (firstBlock pre n)
  else if blocks pre n = 3 then sround3V (firstBlock pre n)
  else ChaCha20.X86_64.Avx2.doubleRoundV

def sroundsV (pre : Bool) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (sroundsV pre n) (sroundV pre n)

/-- `srounds` with `vprold` (AVX-512VL), from and to the registers and slots
`srounds` keeps the words in, as `Avx2.roundsVL`. -/
def sroundsVL (pre : Bool) (n : Nat) : Prog isa :=
  .seq (.block [.vmovdquLoad .l256 .xmm14 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 10)),
    .vmovdquLoad .l256 .xmm15 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 11))])
  (.seq (sroundsV pre n) (.block [.vmovdquStore .l256 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 10)) .xmm14,
    .vmovdquStore .l256 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 11)) .xmm15,
    .vmovdquLoad .l256 .xmm15 (at_ .rcx ChaCha20.X86_64.Avx2.rot16Off)]))

/-- A chunk's ten double rounds, with `vprold` if `vl`. -/
def sroundsFor (vl : Bool) (pre : Bool) : Prog isa :=
  if vl then sroundsVL pre 10 else srounds pre 10

/-- The counter advanced by 8 and 512 bytes fewer left; `CF` is clear if at
least 512 bytes remain. -/
def next : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
   .mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 512), .store (at_ .rcx lenOff) .rdx,
   .alu .cmp .rdx (.imm 512)]

/-- The first chunk, the kernel's (`rsi` stays at it), but for `next`. -/
def firstMain (vl : Bool) : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (ChaCha20.X86_64.Avx2.roundsFor vl) (.block ChaCha20.X86_64.Avx2.finish))

def firstChunk (vl : Bool) : Prog isa := .seq (firstMain vl) (.block next)

/-- A later chunk but for `next`: the 512 bytes at `rsi` (the chunk before)
absorbed during the rounds, then the next 512 encrypted; or (`pre`) the 448
bytes at `rsi` before the first chunk, then the first chunk. -/
def chunkMain (vl pre : Bool) : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (sroundsFor vl pre)
      (.block (([.alu .add .rsi (.imm (BitVec.ofNat 32 (16 * total pre)))] : List Instr) ++
        ChaCha20.X86_64.Avx2.finish)))

def chunk (vl pre : Bool) : Prog isa := .seq (chunkMain vl pre) (.block next)

/-- `r12`–`r14` and the length stashed, the kernel's constants stored, and
the key and the accumulator loaded from the Poly1305 state (`ctx + 448`,
through `rdi`, which then points at the ChaCha20 state again). -/
def enter : List Instr :=
  ([.store (at_ .rcx r12Off) .r12, .store (at_ .rcx r13Off) .r13, .store (at_ .rcx r14Off) .r14,
   .store (at_ .rcx lenOff) .rdx] : List Instr) ++ ChaCha20.X86_64.Avx2.consts ++
  ([.mov .rdi (.reg .rcx), .alu .add .rdi (.imm 320)] : List Instr) ++ Poly1305.X86_64.setup ++
  ([.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)] : List Instr)

/-- The accumulator reduced and stored, `r12`–`r14` and `r15` (the context)
restored, `rbx`, `rbp` the ciphertext not yet absorbed and `rsi`, `rdx` the
data not yet encrypted. -/
def leave : List Instr :=
  Poly1305.X86_64.reduce ++
  ([.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .alu .add .rbp (.imm 512),
   .mov .rdx (.mem (at_ .rcx lenOff)), .alu .add .rsi (.imm 512),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr)

/-! ## The last bytes of `seal`

If 1 to 256 bytes are left after the whole chunks, `tailS` computes their
keystream with `Avx2Tail`'s code for one set of two blocks (up to 128 bytes)
or two sets (up to 256), whose double rounds absorb the 32 blocks of the
last chunk at `rsi`, one after each half of a round (`tround`, as many in
each double round as `chunk`'s); the rounds are bound by their latency, which
the blocks of Poly1305 fill. Its setup reads `buf` through `r9`, which holds
part of the key: `r12`, free until the first block, keeps it meanwhile.
Then `leaveT` stores the accumulator and restores the registers, as `leave`
does, with `rbx`, `rbp` the bytes left (the ciphertext not yet absorbed),
and the keystream, computed into `buf`, is XORed into them. -/

/-- Block `j` of the 512 bytes at `rsi` absorbed. -/
def piece (j : Nat) : List Instr := addProd j ++ Poly1305.X86_64.carryS

/-- `Avx2Tail`'s double round `n`, on one set (`two = false`) or two,
absorbing the `bl n` blocks from `fb n` (a schedule: 0, 3 or 4 blocks a
round): one after each half of the round but the first if three. -/
def troundG (two : Bool) (bl fb : Nat → Nat) (n : Nat) : List Instr :=
  let h := if two then ChaCha20.X86_64.Avx2Tail.half2 else ChaCha20.X86_64.Avx2Tail.half1
  let r := if two then ChaCha20.X86_64.Avx2Tail.rot2 else ChaCha20.X86_64.Avx2Tail.rot1
  let j := fb n + bl n - 4
  if bl n = 0 then
    h .xmm8 12 ++ h .xmm9 7 ++ r 0x39 0x4e 0x93 ++ h .xmm8 12 ++ h .xmm9 7 ++ r 0x93 0x4e 0x39
  else
    h .xmm8 12 ++ (if bl n = 4 then piece j else []) ++ h .xmm9 7 ++ piece (j + 1) ++
      r 0x39 0x4e 0x93 ++ h .xmm8 12 ++ piece (j + 2) ++ h .xmm9 7 ++ piece (j + 3) ++ r 0x93 0x4e 0x39

/-- `n` double rounds, each absorbing its blocks. -/
def troundsG (two : Bool) (bl fb : Nat → Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (troundsG two bl fb n) (.block (troundG two bl fb n))

/-- `troundG` with the schedule of a chunk's rounds (`blocks`). -/
abbrev tround (two pre : Bool) (n : Nat) : List Instr := troundG two (blocks pre) (firstBlock pre) n

abbrev trounds (two pre : Bool) : Nat → Prog isa := troundsG two (blocks pre) (firstBlock pre)

/-- `Avx2Tail`'s lane increments and the masks stored in `buf` (as
`vg_chacha20_xor_avx2` does), and its setup, with `buf` in `r9` meanwhile. -/
def tailA (two : Bool) : List Instr :=
  ChaCha20.X86_64.Avx2Tail.consts ++ ChaCha20.X86_64.Avx2.consts ++
    ([.mov .r12 (.reg .r9), .mov .r9 (.reg .rcx)] : List Instr) ++
    (if two then ChaCha20.X86_64.Avx2Tail.setup else ChaCha20.X86_64.Avx2Tail.setup1) ++
    ([.mov .r9 (.reg .r12)] : List Instr)

/-- As `leave`, with `rbx`, `rbp` the bytes left after the last chunk (or,
`pre`, after the 448 bytes before the first). -/
def leaveT (pre : Bool) : List Instr :=
  Poly1305.X86_64.reduce ++
  ([.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .alu .add .rbx (.imm (BitVec.ofNat 32 (16 * total pre))),
   .mov .rbp (.mem (at_ .rcx lenOff)),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr)

/-- After the rounds: `leaveT`, and the keystream into `buf` (through `r9`),
the `rbp` bytes of it at `rsi` for `xorBufX`. -/
def tailB (two pre : Bool) : List Instr :=
  leaveT pre ++ ([.mov .r9 (.reg .rcx)] : List Instr) ++
    (if two then ChaCha20.X86_64.Avx2Tail.addIn ++ ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      ChaCha20.X86_64.Avx2Tail.storeSet .xmm4 .xmm5 .xmm6 .xmm7 128
    else ChaCha20.X86_64.Avx2Tail.addIn1 ++ ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0) ++
    ([.mov .rsi (.reg .r9), .mov .rdx (.reg .rbp)] : List Instr)

/-- The keystream of the bytes left computed into `buf` while the last chunk
(or, `pre`, the 448 bytes before the first) is absorbed, and the registers
restored. -/
def tailAB (two pre : Bool) : Prog isa :=
  .seq (.block (tailA two)) (.seq (trounds two pre 10) (.block (tailB two pre)))

/-- The bytes left (1 to 128, or 129 to 256 with `two`) encrypted, the last
chunk (or, `pre`, the 448 bytes before the first) absorbed, and `rdx` 0
(nothing left to encrypt) with `buf` in `rcx`. The `test` gives `xorBufX`
flags computed from the length. -/
def tailS (two pre : Bool) : Prog isa :=
  .seq (tailAB two pre)
  (.seq (.block [.alu .test .rdx (.reg .rdx)])
  (.seq (xorBufX 5 .rbx)
    (.block [.vop .vzeroupper, .mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)])))

/-- `n` bytes (not 1) of instructions that only write `r`, from what it
held or 0: `mov r32, 0` (5 bytes, for `rax` to `rdi`), `mov r64, r64` (3)
and `mov r32, r32` (2). They pad code so that what follows keeps its offsets
modulo 32 when code is added before it (`restT`, `tailK`, `restO`, `cryptO`, `decRest`): on
Cascade Lake, whose microcode mitigates the JCC erratum, a shift of the
code for the lengths an addition does not touch made them up to 2% slower. -/
def padIns (r : Reg) : Nat → List Instr
  | 0 => []
  | 2 => [.mov32 r (.reg r)]
  | 3 => [.mov r (.reg r)]
  | 4 => [.mov32 r (.reg r), .mov32 r (.reg r)]
  | 6 => [.mov r (.reg r), .mov r (.reg r)]
  | n + 5 => .mov32 r (.imm 0) :: padIns r n
  | _ => []

/-! ### 257 to 448 bytes left

`tailK` computes the keystream of eight blocks, as a chunk does, while its
rounds absorb the last chunk (or, `pre`, the 448 bytes before the first, with
up to 512 bytes left); but it stores the keystream to `ctx + 736` (`buf +
608`, `kOff`), past the Poly1305 state, unused once the prologue's keystream
is XORed into the data (`cryptPre`), and XORs the bytes left into the data
from there, as `tailS` does from `buf`. So
`macPadLengths` absorbs only the bytes left, not the last chunk too, and
there is no call of `vg_chacha20_xor`. -/

/-- Where `tailK` stores the keystream, from `buf`. -/
def kOff : Nat := 608

/-- Row `row` of the eight blocks, transposed into `xs` (as for `xorRow`),
stored to `buf + off`: block `i` at `off + 64 i`. -/
def storeRow (off row : Nat) (xs : List XReg) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.vmovdquStore .l128 (at_ .rcx (off + 64 * i + 16 * row)) (xs.getD i .xmm0),
     .vop (.vextracti128 .xmm13 (xs.getD i .xmm0) 1),
     .vmovdquStore .l128 (at_ .rcx (off + 64 * (i + 4) + 16 * row)) .xmm13]

/-- The eight blocks' keystream stored at `buf + kOff` while the 512 bytes
at `rsi` (the last chunk) are absorbed. -/
def tailKMain (vl pre : Bool) : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
  (.seq (sroundsFor vl pre) (.block (ChaCha20.X86_64.Avx2.finishWith (storeRow kOff))))

/-- `tailK`'s moves: `buf` into `r9`, the stored keystream into `rsi`, the
bytes left into `rdx`. -/
def movK : List Instr :=
  [.mov .r9 (.reg .rcx), .mov .rsi (.reg .rcx), .alu .add .rsi (.imm (BitVec.ofNat 32 kOff)),
   .mov .rdx (.reg .rbp)]

/-- `tailKMain`, then `leaveT` and `movK`: `tailK` but for the XOR. -/
def tailKAB (vl pre : Bool) : Prog isa :=
  .seq (tailKMain vl pre) (.block (leaveT pre ++ movK))

/-- `tailKAB`; then the bytes left encrypted from the stored keystream, as
`tailS` does from `buf`. -/
def tailKX (vl pre : Bool) : Prog isa :=
  .seq (tailKAB vl pre)
  (.seq (.block [.alu .test .rdx (.reg .rdx)])
  (.seq (xorBufX 5 .rbx)
    (.block [.vop .vzeroupper, .mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)])))

/-- 257 to 448 bytes left: `tailKX`, padded (with `rax`, dead here) so that
with the padding before `restT`'s comparison with 448 the code after it keeps
its offsets modulo 32. -/
def tailK (vl : Bool) : Prog isa :=
  .seq (tailKX vl false) (.block (padIns .rax 29))

/-- After the whole chunks: if 1 to 256 bytes are left, `tailS`; if 257 to
448, `tailK`; otherwise `leave`. -/
def restT (vl : Bool) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 1), .alu .cmp .rdx (.imm 256)])
  (.ite .b
    (.seq (.block [.alu .cmp .rdx (.imm 128)]) (.ite .b (tailS false false) (tailS true false)))
    (.seq (.block (padIns .rax 19 ++ ([.alu .cmp .rdx (.imm 448)] : List Instr))) (.ite .b (tailK vl) (.block leave))))

/-- The whole chunks of at least 512 bytes of data, and the rest if at most
256 bytes. -/
def bulk (vl : Bool) : Prog isa :=
  .seq (.block enter)
  (.seq (firstChunk vl)
  (.seq (.ite .b (.block []) (.loop (chunk vl false) .ae))
    (restT vl)))

/-- As `bulk`, after the first 448 bytes are encrypted from the prologue's
keystream (`rsi` at them): the first chunk absorbs them, and the rest is as
`bulk`'s. -/
def bulkP (vl : Bool) : Prog isa :=
  .seq (.block enter)
  (.seq (chunk vl true)
  (.seq (.ite .b (.block []) (.loop (chunk vl false) .ae))
    (restT vl)))

/-- The data and the ciphertext to absorb when there are no whole chunks:
all of it. -/
def whole : List Instr := [.mov .rbx (.reg .r14), .mov .rbp (.reg .r13)]

/-- More than `fold` bytes, none of whose keystream the prologue computed:
the whole chunks, and the rest if at most 256 bytes, by `bulk`. -/
def bigS (vl : Bool) : Prog isa :=
  .seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.ite .b (.block whole) (bulk vl))

/-- After `enter`, with no whole chunk after the first 448 bytes: the rest
(1 to 512 bytes) encrypted while they are absorbed, by `tailS` (up to 128
bytes, or 256 with two sets of blocks) or by `tailKX` (eight blocks). -/
def tailP (vl : Bool) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 1), .alu .cmp .rdx (.imm 256)])
    (.ite .b
      (.seq (.block [.alu .cmp .rdx (.imm 128)]) (.ite .b (tailS false true) (tailS true true)))
      (tailKX vl true))

/-- More than `fold` bytes, the keystream of whose first `m` (448) the
prologue computed: those by `cryptPre`, then the whole chunks after them by
`bulkP`, or, if there are none (at most 512 bytes after them), the rest by
`tailP`, which absorbs the first 448. -/
def preS (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (cryptPre x.fold x.pass x.wide)
  (.seq (.block [.mov .rsi (.reg .r14), .alu .cmp .rdx (.imm 513)])
    (.ite .b (.seq (.block enter) (tailP x.vl)) (bulkP x.vl)))

/-! ### `open`'s prologue

With more than `fold` (448) bytes of data, `open`'s prologue computes the
one-time key's block with the block of the last bytes in the two lanes of
`Avx2Tail`'s code for one set of two blocks (`twoKs`), or with the three
blocks of 65 to 192 bytes after the whole chunks in two sets (`fourKs`),
rather than calling `vg_chacha20_xor` for the key's block alone, which on a
Zen 3 (EPYC 7763) costs about 20 ns more: its AVX2 code passes one block to
the scalar code, which calls `vg_chacha20_block`. `decRest` decrypts 1 to 192
bytes after the whole chunks from those blocks; for other lengths `twoKs`'s
second block goes unused. (`seal` gains nothing from it: its tail's rounds,
`tailS`, run while the last chunk is absorbed.) -/

/-- `CF` set if the data's length (`r13`) is at most `fold` (448), for which
the prologue calls `vg_chacha20_xor`; `rax` is `(len - 1) mod 512`. -/
def xTest : List Instr :=
  [.mov .rax (.reg .r13), .alu .sub .rax (.imm 1), .alu .and .rax (.imm 511), .alu .cmp .r13 (.imm 449)]

/-- `CF` set if `rax` is from 64 to 191 (`rax - 64 < 128`, unsigned): 65 to
192 bytes after the whole chunks, whose three blocks `fourKs` computes. -/
def fTest : List Instr := [.alu .sub .rax (.imm 64), .alu .cmp .rax (.imm 128)]

/-- The constants of `twoKs`, at `rcx` (`ctx + 672`): the masks
(`Avx2.consts`), and the first set's lane increments, `0` and the counter of
the block of the last bytes, `1 + 8 ⌊len / 512⌋` (as a doubleword: the
counter wraps around as ChaCha20's does). -/
def twoConsts : List Instr :=
  ChaCha20.X86_64.Avx2Tail.storeQ 224 [0, 0, 0, 0] ++
    [.mov .rax (.reg .r13), .shift .shr .rax 9, .shift .shl .rax 3, .alu .add .rax (.imm 1),
     .store32 (at_ .rcx 240) .rax] ++ ChaCha20.X86_64.Avx2.consts

/-- `twoConsts` and the second set's lane increments, the next two blocks'
counters. -/
def fourConsts : List Instr :=
  ChaCha20.X86_64.Avx2Tail.storeQ 224 [0, 0, 0, 0] ++ ChaCha20.X86_64.Avx2Tail.storeQ 256 [0, 0, 0, 0] ++
    [.mov .rax (.reg .r13), .shift .shr .rax 9, .shift .shl .rax 3, .alu .add .rax (.imm 1),
     .store32 (at_ .rcx 240) .rax, .alu .add .rax (.imm 1), .store32 (at_ .rcx 256) .rax,
     .alu .add .rax (.imm 1), .store32 (at_ .rcx 272) .rax] ++ ChaCha20.X86_64.Avx2.consts

/-- The keystream of the one-time key's block and of the block of the last
bytes into `ctx[672, 800)`, from the state at `rdi` (`ctx + 608`, counter 0),
with `buf` for `Avx2Tail`'s code at `ctx + 672` (its constants past the
keystream); then `rsi` at `buf`, as the call of `vg_chacha20_xor` leaves it. -/
def twoKsB (vl : Bool) : Prog isa :=
  .seq (.block (ptr .rcx .r15 672 ++ twoConsts ++ ([.mov .r9 (.reg .rcx)] : List Instr)))
  (.seq (.seq (.block ChaCha20.X86_64.Avx2Tail.setup1) (.seq (ChaCha20.X86_64.Avx2Tail.roundsS vl 1 10)
      (.block (ChaCha20.X86_64.Avx2Tail.addIn1 ++ ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0))))
    (.block (([.vop .vzeroupper] : List Instr) ++ ptr .rsi .r15 128)))

/-- `twoKsB`, padded to keep the code after the prologue at its offset
modulo 64 before `twoKs` replaced the call past 448 bytes (Zen 3 ran `open`'s
code for 16 to 448 bytes, and the tail of 193 to 256 bytes, up to 2% slower
when it moved by 9 bytes). -/
def twoKs (vl : Bool) : Prog isa :=
  .seq (twoKsB vl) (.block (padIns .rax 9))

/-- As `twoKs` with two sets: the one-time key's block and the three blocks
of the last 65 to 192 bytes into `ctx[672, 928)`. -/
def fourKs (vl : Bool) : Prog isa :=
  .seq (.block (ptr .rcx .r15 672 ++ fourConsts ++ ([.mov .r9 (.reg .rcx)] : List Instr)))
  (.seq (.seq (.block ChaCha20.X86_64.Avx2Tail.setup) (.seq (ChaCha20.X86_64.Avx2Tail.roundsS vl 2 10)
      (.block (ChaCha20.X86_64.Avx2Tail.addIn ++ ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++
        ChaCha20.X86_64.Avx2Tail.storeSet .xmm4 .xmm5 .xmm6 .xmm7 128))))
    (.block (([.vop .vzeroupper] : List Instr) ++ ptr .rsi .r15 128)))

/-- `prologue`, by `twoKs` or `fourKs` instead of the call of
`vg_chacha20_xor` past `fold` bytes. -/
def prologueX (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (prologueA x.fold x.pass x.wide)
  (.seq (.seq (.block xTest) (.ite .b (.call x.name x.code)
    (.seq (.block fTest) (.ite .b (fourKs x.vl) (twoKs x.vl))))) prologueB)

/-- `crypt`, with `rbx`, `rbp` set to the ciphertext not yet absorbed: the
whole chunks are encrypted and absorbed by `bigS` or `preS`, with the rest if
at most 256 bytes, and any rest left encrypted by the implementation `x` of
`vg_chacha20_xor`. `m` is the prologue's (`mLoad`). Then the keystream is
wiped: past `fold` bytes all of `ctx[672, 1248)`, where `tailK` stores its
own too (`wipeL`). -/
def cryptS (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))])
  (.seq (.ite .b
    (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX x.wide .r14) (.block (ptr .rsi .r15 128 ++ whole))))
    (.seq (.block mLoad)
    (.seq (.block [.alu .test .rdx (.reg .rdx)])
      (.seq (.ite .e (bigS x.vl) (preS x))
        (.seq (.block [.alu .test .rdx (.reg .rdx)])
          (.ite .e (.block [.mov .rsi (.reg .rcx)]) (.call x.name x.code)))))))
  (.seq (.block (anchor .rsi 128))
  (.seq (wipeL x.fold 512)
  (.seq (.block [.alu .add .rdx (.imm 64)]) (zeroKs x.wide)))))

/-- `seal`, with Poly1305 inside the kernel for the whole chunks. -/
def sealStitched (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue x)
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq (cryptS x)
  (.seq (macPadLengths b .rbx .rbp)
  (.seq finalizeTag
    (.block restore)))))))

/-- The AVX-512 instances (without IFMA) seal fewer bytes of data than this
with the AVX2 code (`sealSmall`), with AVX-512VL's rounds (`vl`) or without:
on Cascade Lake, with them it is the faster up to 767 bytes (by up to 6.4%
from 640 on), and from 768 on the AVX-512 code is, even with its lower clock
(the AVX2 code is 25-30% slower at 800-831 bytes); without them, the AVX-512
code is the faster from 640 on. -/
def smallLim (vl : Bool) : Nat := if vl then 768 else 640

/-- The lengths from `winLo` to `winHi - 1` the AVX-512 instances (without
IFMA) also seal and open with the AVX2 code: the AVX-512 code computes their
keystream in two passes of sixteen blocks (the one-time key's, which the
data's 961 bytes or more no longer fit after (`fold` 960), and the data's),
the AVX2 code in fewer blocks. -/
def winLo : Nat := 961
def winHi : Nat := 1025

/-- `CF` set if `len` (`r9`) is below `lim` or in `[winLo, winHi)`: `rax`
is `len`, or 0 in the window (unsigned, `len - winLo < winHi - winLo`), and
is compared with `lim`; `rax` and `r10` are scratch. The first instruction,
`mov eax, 0` (5 bytes), only pads the test to 39 bytes, 32 more than the
`cmp r9, lim` it replaced, so that the code after it, and every function
after it, keeps its offsets modulo 32: on Cascade Lake (whose microcode
mitigates the JCC erratum), moving the AVX-512 code by 27 bytes made seal
1-2.6% slower at 896 to 960 bytes. -/
def smallTest (lim : Nat) : List Instr :=
  [.mov32 .rax (.imm 0), .mov .rax (.reg .r9), .mov .r10 (.reg .r9), .alu .sub .r10 (.imm (BitVec.ofNat 32 winLo)),
   .alu .cmp .r10 (.imm (BitVec.ofNat 32 (winHi - winLo))), .mov .r10 (.imm 0),
   .cmov .b .rax (.reg .r10), .alu .cmp .rax (.imm (BitVec.ofNat 32 lim))]

/-- `seal` for fewer than `smallLim` bytes of data (`len`, in `r9`), or from
`winLo` to `winHi - 1`, with the AVX2
code, `sealStitched` with the implementation `small` of `vg_chacha20_xor`
(`vg_chacha20_xor_avx2`, or `vg_chacha20_xor_avx512vl`, which keeps that
data in `ymm` registers) and `vg_poly1305_blocks_avx2`, which runs no
512-bit instruction, and for more with `big`. On CPUs whose
clock drops while they run 512-bit instructions (Skylake-SP, Cascade Lake:
the AVX-512 implementations without IFMA), that slows the whole of `seal`
for short data more than the 16-block keystream gains. -/
def sealSmall (small : ChaCha20.X86_64.Callee) (big : Prog isa) : Prog isa :=
  .seq (.block (smallTest (smallLim small.vl)))
    (.ite .b (sealStitched { small with pass := 512 } .avx2) big)

/-- The `seal` an instance uses: with the AVX2 implementation of
`vg_poly1305_blocks` (whose ChaCha20 is the AVX2 kernel), `sealStitched`,
whose prologue computes the keystream of the first 448 bytes too when the
rest is whole chunks and 1 to 64 bytes, or the data is shorter than 1409
bytes (`pass` 512, `splitM`); with the
AVX-512 one (without IFMA), `sealSmall` of `seal`; otherwise `seal`. -/
def sealFor (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx2 => sealStitched { x with pass := 512 } .avx2
  | .avx512 => sealSmall x.small («seal» x .avx512)
  | b => «seal» x b

/-! ## `open`

`open` absorbs the ciphertext before it decrypts it, so each chunk absorbs
its own 512 bytes during its rounds, before the kernel's `finish` XORs the
keystream into them: no chunk is special. `bulkO` runs them while at least
512 bytes remain; `leaveO` leaves `rbx`, `rbp` and `rsi`, `rdx` at the rest,
which `cryptO` absorbs (with the lengths block) before the call of
`vg_chacha20_xor` decrypts it. Below 512 bytes (449 to 511, past `fold`),
`wholeO` runs the kernel once, absorbing the first 448 bytes while it stores
the keystream of all of them at `ctx + 736`. -/

/-- A chunk of `open` but for `next`: the 512 bytes at `rsi` absorbed during
the rounds, then decrypted, and `rsi` advanced past them. -/
def chunkMainO (vl : Bool) : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (sroundsFor vl false)
      (.block (ChaCha20.X86_64.Avx2.finish ++ ([.alu .add .rsi (.imm 512)] : List Instr))))

def chunkO (vl : Bool) : Prog isa := .seq (chunkMainO vl) (.block next)

/-- As `leave`, with the rest of the data both the ciphertext not yet
absorbed (`rbx`, `rbp`) and the data not yet decrypted (`rsi`, `rdx`). -/
def leaveO : List Instr :=
  Poly1305.X86_64.reduce ++
  [.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .mov .rdx (.mem (at_ .rcx lenOff)),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]

/-! ### The last bytes of `open`

With 65 to 256 bytes left after the whole chunks, `tailO` computes their
keystream with `Avx2Tail`'s code (one set of two blocks up to 128 bytes, two
sets above), whose rounds absorb their first `k` blocks (4, 8 or 12: as many
as they surely have), four a round (`oblocks`); `leaveTO` leaves `rbx`,
`rbp` at the bytes after those, which `cryptO` absorbs with the lengths
block before it XORs the keystream, computed into `buf`, into the bytes
left (`decRest`). -/

/-- The blocks round `n` of `tailO` absorbs: four in each of the first
`k / 4`. -/
def oblocks (k n : Nat) : Nat := if n < k / 4 then 4 else 0
def ofirst (k n : Nat) : Nat := 4 * min n (k / 4)

/-- As `leaveO`, with `rbx`, `rbp` the bytes left after the first `k` blocks
of the `[lenOff]` bytes at `rsi`. -/
def leaveTO (k : Nat) : List Instr :=
  Poly1305.X86_64.reduce ++
  [.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .alu .add .rbx (.imm (BitVec.ofNat 32 (16 * k))),
   .mov .rbp (.mem (at_ .rcx lenOff)), .alu .sub .rbp (.imm (BitVec.ofNat 32 (16 * k))),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]

/-- After the rounds: `leaveTO`, and the keystream into `buf` (through `r9`). -/
def tailBO (two : Bool) (k : Nat) : List Instr :=
  leaveTO k ++ ([.mov .r9 (.reg .rcx)] : List Instr) ++
    (if two then ChaCha20.X86_64.Avx2Tail.addIn ++ ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      ChaCha20.X86_64.Avx2Tail.storeSet .xmm4 .xmm5 .xmm6 .xmm7 128
    else ChaCha20.X86_64.Avx2Tail.addIn1 ++ ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0) ++
    ([.vop .vzeroupper] : List Instr)

/-- The keystream of the bytes left (at most 128, or 256 with `two`)
computed into `buf` while their first `k` blocks are absorbed, and the
registers restored. -/
def tailO (two : Bool) (k : Nat) : Prog isa :=
  .seq (.block (tailA two)) (.seq (troundsG two (oblocks k) (ofirst k) 10) (.block (tailBO two k)))

/-- More than `fold` (448) bytes but no whole chunk (449 to 511): the
kernel's eight blocks of keystream stored at `buf + kOff` (`ctx + 736`) while
the first 448 bytes of ciphertext, at `rsi`, are absorbed (`tailKMain` with
`pre`), then `leaveTO`, `rbx`, `rbp` at the rest, which `cryptO` absorbs with
the lengths block before `decRest` decrypts the data from that keystream. -/
def wholeO (vl : Bool) : Prog isa :=
  .seq (.block enter) (.seq (tailKMain vl true) (.block (leaveTO 28 ++ ([.vop .vzeroupper] : List Instr))))

/-! With 257 to 511 bytes left after the whole chunks, their keystream is
stored at `buf + kOff` (`ctx + 736`), where `decRest` decrypts them from and
then wipes it, as `wholeO`'s: up to 384 bytes, six blocks by `Avx2Tail`'s
code for three sets (`tail3O`, as `tailO`), whose rounds absorb the first
16 blocks; from 385, the kernel's eight (`tailKO`, as `wholeO`), whose
rounds absorb the first 24. Their rounds are two loops (`roundsL`), not
unrolled as a chunk's: one of the rounds that absorb four blocks each and
one of the others, so that the two tails add 5 KB of code to `open` rather
than 19 KB (Zen 3 ran `open`'s code for the other lengths up to 4% slower,
and a seal benchmark whose code it did not change 3% slower, with the
larger code). -/

/-- `Avx2Tail`'s double round `n` on three sets, absorbing the `bl n` blocks
from `fb n`, as `troundG`. -/
def troundG3 (bl fb : Nat → Nat) (n : Nat) : List Instr :=
  let h := ChaCha20.X86_64.Avx2Tail.half3
  let r := ChaCha20.X86_64.Avx2Tail.rot3
  let j := fb n + bl n - 4
  if bl n = 0 then
    h .xmm14 12 ++ h .xmm15 7 ++ r 0x39 0x4e 0x93 ++ h .xmm14 12 ++ h .xmm15 7 ++ r 0x93 0x4e 0x39
  else
    h .xmm14 12 ++ (if bl n = 4 then piece j else []) ++ h .xmm15 7 ++ piece (j + 1) ++
      r 0x39 0x4e 0x93 ++ h .xmm14 12 ++ piece (j + 2) ++ h .xmm15 7 ++ piece (j + 3) ++ r 0x93 0x4e 0x39

/-- `r` then `a`, `rdi` times (at least once): the counter is `rdi`, which
no round reads, and which `roundsL` points at the state again after. -/
def cntLoop (r : Prog isa) (a : List Instr) : Prog isa :=
  .loop (.seq (.seq r (.block a)) (.block [.alu .sub .rdi (.imm 1)])) .ne

/-- Ten double rounds absorbing the first `k` blocks at `rsi` (`k / 4` rounds
`r4` of four blocks each, then `10 - k / 4` rounds `r0`), with `rsi` back at
them and `rdi` at the state (`buf - 64`) after. -/
def roundsL (r4 r0 : Prog isa) (k : Nat) : Prog isa :=
  .seq (.block [.mov32 .rdi (.imm (BitVec.ofNat 32 (k / 4)))])
  (.seq (cntLoop r4 [.alu .add .rsi (.imm 64)])
  (.seq (.block [.alu .sub .rsi (.imm (BitVec.ofNat 32 (16 * k))),
    .mov32 .rdi (.imm (BitVec.ofNat 32 (10 - k / 4)))])
  (.seq (cntLoop r0 [])
    (.block [.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)]))))

/-- As `tailA`, with `Avx2Tail`'s setup of three sets. -/
def tailA3 : List Instr :=
  ChaCha20.X86_64.Avx2Tail.consts ++ ChaCha20.X86_64.Avx2.consts ++
    ([.mov .r12 (.reg .r9), .mov .r9 (.reg .rcx)] : List Instr) ++ ChaCha20.X86_64.Avx2Tail.setup3 ++
    ([.mov .r9 (.reg .r12)] : List Instr)

/-- `Avx2Tail.storeSetT` to `rsi + off`. -/
def storeSetS (a b c d : XReg) (off : Nat) : List Instr :=
  [.vop (.vperm2i128 .xmm12 a b 0x20), .vmovdquStore .l256 (at_ .rsi off) .xmm12,
   .vop (.vperm2i128 .xmm12 c d 0x20), .vmovdquStore .l256 (at_ .rsi (off + 32)) .xmm12,
   .vop (.vperm2i128 .xmm12 a b 0x31), .vmovdquStore .l256 (at_ .rsi (off + 64)) .xmm12,
   .vop (.vperm2i128 .xmm12 c d 0x31), .vmovdquStore .l256 (at_ .rsi (off + 96)) .xmm12]

/-- After the rounds: `leaveTO`, and the six blocks' keystream at
`ctx + 736` (`buf + kOff`), through `rsi`, which the rest of `cryptO` sets
before it reads it. -/
def tailBO3 (k : Nat) : List Instr :=
  leaveTO k ++ ([.mov .r9 (.reg .rcx)] : List Instr) ++ ptr .rsi .r15 736 ++ ChaCha20.X86_64.Avx2Tail.addIn3 ++
    storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++
    storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256 ++ ([.vop .vzeroupper] : List Instr)

/-- The keystream of the bytes left (at most 384) stored at `buf + kOff`
while their first `k` blocks are absorbed, and the registers restored. -/
def tail3O (k : Nat) : Prog isa :=
  .seq (.block tailA3) (.seq (roundsL (.block (troundG3 (oblocks 4) (ofirst 4) 0))
    (.block (troundG3 (oblocks 0) (ofirst 0) 0)) k) (.block (tailBO3 k)))

/-- `roundsL` of the kernel's double rounds, with `vprold` if `vl` (in
`ymm14` and `ymm15` meanwhile, as `sroundsVL`). -/
def roundsLK (vl : Bool) (k : Nat) : Prog isa :=
  if vl then
    .seq (.block [.vmovdquLoad .l256 .xmm14 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 10)),
      .vmovdquLoad .l256 .xmm15 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 11))])
    (.seq (roundsL (sround4V 0) ChaCha20.X86_64.Avx2.doubleRoundV k)
      (.block [.vmovdquStore .l256 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 10)) .xmm14,
        .vmovdquStore .l256 (at_ .rcx (ChaCha20.X86_64.Avx2.slotOff 11)) .xmm15,
        .vmovdquLoad .l256 .xmm15 (at_ .rcx ChaCha20.X86_64.Avx2.rot16Off)]))
  else roundsL (sround4 0) ChaCha20.X86_64.Avx2.doubleRound k

/-- The kernel's eight blocks of keystream stored at `buf + kOff` while the
first `k` blocks of the bytes left are absorbed, then `leaveTO`. -/
def tailKO (vl : Bool) (k : Nat) : Prog isa :=
  .seq (.seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (roundsLK vl k) (.block (ChaCha20.X86_64.Avx2.finishWith (storeRow kOff)))))
  (.block (leaveTO k ++ ([.vop .vzeroupper] : List Instr)))

/-- After the whole chunks, with `rdx` the bytes left less 193: with 193 to
256 left, `tailO` (12 blocks absorbed); with 257 to 384, `tail3O` (16);
with 385 to 511, `tailKO` (24); otherwise `leaveO` (the prologue computed the
keystream of 1 to 192 bytes left, `twoKs` or `fourKs`). The tails are out of
line and `leaveO` falls through at its offset before them: the first test
(193 to 511 left) has the length of the one it replaced, and the padding of
`tailKO` (longer with `vprold`, whose rounds are shorter) keeps the code
after the tails at its offset modulo 64 (Zen 3 and Zen 4 ran the chunks'
code up to 2% slower when it moved). -/
def restO (vl : Bool) : Prog isa :=
  .seq (.block (padIns .rdx 5 ++
    ([.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 193), .alu .cmp .rdx (.imm 319)] : List Instr)))
  (.ite .b
    (.seq (.block [.alu .cmp .rdx (.imm 64)])
      (.ite .b (tailO true 12)
        (.seq (.block [.alu .cmp .rdx (.imm 192)])
          (.ite .b (tail3O 16) (.seq (tailKO vl 24) (.block (padIns .rax (if vl then 35 else 19))))))))
    (.block leaveO))

/-- The whole chunks of at least 512 bytes of data, decrypted and absorbed,
and of 193 to 511 bytes after them the first blocks absorbed and the
keystream computed. -/
def bulkO (vl : Bool) : Prog isa :=
  .seq (.block enter) (.seq (.loop (chunkO vl) .ae) (restO vl))

/-- The arguments of the call on the rest of the data (`rbx`, `rbp`), from
the counter the chunks left. -/
def restArgs : List Instr :=
  ptr .rdi .r15 64 ++ [.mov .rsi (.reg .rbx), .mov .rdx (.reg .rbp)] ++ ptr .rcx .r15 128

/-- The rest decrypted from its keystream at `ctx + o`: the `len mod 512`
bytes after the whole chunks; `rsi` then at `buf`. -/
def xorTail (w o : Nat) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .r13), .alu .and .rdx (.imm 511), .mov .r10 (.reg .r14),
    .alu .add .r10 (.reg .r13), .alu .sub .r10 (.reg .rdx)] ++ ptr .rsi .r15 o))
    (.seq (xorBufX w .r10) (.block (ptr .rsi .r15 128)))

/-- `CF` set if `len mod 512` (`r13`) is from `lo` to `lo + n - 1`. -/
def restTest (lo n : Nat) : List Instr :=
  [.mov .rax (.reg .r13), .alu .and .rax (.imm 511), .alu .sub .rax (.imm (BitVec.ofNat 32 lo)),
   .alu .cmp .rax (.imm (BitVec.ofNat 32 n))]

/-- The rest decrypted: below 512 bytes all of the data, from the keystream
`wholeO` stored at `ctx + 736`, which is then wiped (`ctx[672, 1248)`: the
wipe after `cryptO` covers only `ctx[672, 800)` past `fold` bytes); from
`buf` if `tailO` computed its keystream (193 to 256 bytes after the whole
chunks), from `ctx + 736` if the prologue did (`twoKs`, `fourKs`: 1 to 192
after them) or `tail3O` or `tailKO` (257 to 511, then wiped), otherwise (none)
by the implementation `x` of `vg_chacha20_xor` from the counter the chunks
left. The call falls through at its offset before the tails were added, and
the padding of the wipe keeps the code after the branches at its offset
modulo 64. -/
def decRest (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm 512)])
  (.ite .b (.seq (xorTail x.wide 736) (.seq (.block [.mov32 .rdx (.imm 576)]) (zeroKs x.wide)))
    (.seq (.seq (.block (restTest 193 64))
      (.ite .b (xorTail x.wide 128)
        (.seq (.block (restTest 1 511))
          (.ite .b
            (.seq (xorTail x.wide 736) (.seq (.block (restTest 257 255))
              (.ite .b (.seq (.block [.mov32 .rdx (.imm 576)])
                (.seq (zeroKs x.wide) (.block (padIns .rax 3)))) (.block []))))
            (.seq (.block restArgs) (.call x.name x.code))))))
      (.block (padIns .rax 20))))

/-- `open`'s `macPadLengths` and `crypt`: if the data is at most `fold`
bytes, as `open` does; otherwise the whole chunks decrypted and absorbed by
`bulkO` (or, below 512 bytes, the first 448 absorbed by `wholeO`), then the
rest absorbed and decrypted. Then the keystream is wiped:
past `fold` bytes `ctx[672, 800)`, where `twoKs` stores the block of the last
bytes too (`wipeL`). -/
def cryptO (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))])
  (.seq (.ite .b
    (.seq (macPadLengths b .r14 .r13)
      (.seq (.block (ptr .rsi .r15 736 ++ [.mov .rdx (.reg .r13)]))
        (.seq (xorBufX x.wide .r14) (.block (ptr .rsi .r15 128)))))
    (.seq (.block (cryptArgs ++ [.alu .cmp .rdx (.imm 512)]))
      (.seq (.ite .b (wholeO x.vl) (bulkO x.vl))
      (.seq (.block (padIns .rax 18))
      (.seq (macPadLengths b .rbx .rbp)
      (decRest x))))))
  (.seq (.block (anchor .rsi 128))
  (.seq (wipeL x.fold 192)
  (.seq (.block [.alu .add .rdx (.imm 64)]) (zeroKs x.wide)))))

/-- `open`, with Poly1305 inside the kernel for the whole chunks. -/
def openStitched (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologueX x)
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq (cryptO x b)
  (.seq (finalizeTo 48)
    (.block (compare ++ restore)))))))

/-- `openSmall`'s limit, as `smallLim` is `sealSmall`'s: on Cascade Lake,
`open`'s AVX2 code with AVX-512VL's rounds (`vl`) is the faster below 768
bytes, from 3.8% to 8.5% from 640 on, and from 768 the AVX-512 code is;
without them, the AVX-512 code is the faster from 640 on. -/
def openLim (vl : Bool) : Nat := if vl then 768 else 640

/-- `open` for fewer than `openLim` bytes of data (`len`, in `r9`), or from `winLo`
to `winHi - 1`, with the
AVX2 code, `openStitched` with the implementation `small` of
`vg_chacha20_xor` and `vg_poly1305_blocks_avx2`, which runs no 512-bit
instruction, and for more with `big`: as `sealSmall`. -/
def openSmall (small : ChaCha20.X86_64.Callee) (big : Prog isa) : Prog isa :=
  .seq (.block (smallTest (openLim small.vl)))
    (.ite .b (openStitched small .avx2) big)

/-- The lengths from `ifmaLo` to `ifmaHi - 1` the IFMA instance opens with the
AVX2 code, with AVX-512VL's rounds (`openWin`). From 449 bytes its own
`open` computes the one-time key's block and the data's in a pass of twelve
blocks (`Avx512Tail.part3`), and from 448 absorbs the ciphertext with
`vg_poly1305_blocks_ifma`, whose powers cost as much as a few hundred bytes;
one after the other, while the AVX2 code absorbs the ciphertext with the
scalar Poly1305 inside its ChaCha20 rounds. On an Intel Xeon with
AVX512_IFMA, the AVX2 code is 9-17% faster from 449 to 639 bytes (the medians
of ten runs), 2-5% from 640 to 704, and slower below 449 and from 705 on;
its `seal` gains less than 5% beyond 449 bytes, so `seal` keeps its own code. -/
def ifmaLo : Nat := 449
def ifmaHi : Nat := 640

/-- `CF` set if `len` (`r9`) is from `ifmaLo` to `ifmaHi - 1` (unsigned,
`len - ifmaLo < ifmaHi - ifmaLo`); `rax` is scratch. -/
def ifmaTest : List Instr :=
  [.mov .rax (.reg .r9), .alu .sub .rax (.imm (BitVec.ofNat 32 ifmaLo)),
   .alu .cmp .rax (.imm (BitVec.ofNat 32 (ifmaHi - ifmaLo)))]

/-- `open` for `ifmaLo` to `ifmaHi - 1` bytes of data with the AVX2 code,
`openStitched` with the implementation `small` of `vg_chacha20_xor` and
`vg_poly1305_blocks_avx2`, and otherwise with `big`. -/
def openWin (small : ChaCha20.X86_64.Callee) (big : Prog isa) : Prog isa :=
  .seq (.block ifmaTest) (.ite .b (openStitched small .avx2) big)

/-- The `open` an instance uses, as `sealFor`: with the AVX2 implementation of
`vg_poly1305_blocks`, `openStitched`; with the AVX-512 one (without IFMA),
`openSmall` of `open`; with the IFMA one, `openWin` of `open`, with
`vg_chacha20_xor_avx512vl`'s rounds; otherwise `open`. -/
def openFor (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx2 => openStitched x .avx2
  | .avx512 => openSmall x.small («open» x .avx512)
  | .ifma => openWin ChaCha20.X86_64.Callee.avx512vl.small («open» x .ifma)
  | b => «open» x b

end VG.Impl.ChaCha20Poly1305.X86_64.Stitch
