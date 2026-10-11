module

public import VerifiedGarbage.Impl.ChaCha20.X86

/-!
# ChaCha20 keystream XOR: x86 (32-bit) implementation

`vg_chacha20_xor(state, data, len, buf)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

While more than 64 bytes remain, four blocks of keystream (the counters
`c, c + 1, c + 2, c + 3` modulo 2³², `c` being word 12 of the state) are
computed at once with SSE2 and XORed into the next 256 bytes, or into all
that remain if fewer (`body4`):

* Word `k` of the four states is kept in its slot, `buf[16 k, 16 k + 16)`,
  doubleword `l` for block `l`, or in an XMM register: each row of the
  state is broadcast from `state` with `pshufd` into the slots, and the four
  counters, computed in `eax`, are written to the slot of word 12 and to
  `buf[272, 288)`.
* The rounds keep seven of the sixteen words in `xmm0, …, xmm6` (`cached`,
  loaded from their slots first and stored back at the end), and each
  quarter round (`vqr`, through `xmm7`) loads the words it needs that are
  not in registers and stores those that the next ones do not need soon
  (`plan`): words 0 and 3 stay in registers throughout, and the others
  between two quarter rounds close enough together, so that a double round
  loads and stores 18 words instead of 32. The ten double rounds are
  unrolled.
* At the end, each row of the four states is loaded, the input states are
  added (their rows broadcast again from `state`, through `xmm4` and
  `xmm5`, and the counters reloaded from `buf[272, 288)`), the four
  registers are transposed (`punpck{l,h}{dq,qdq}`, through `xmm4` and
  `xmm5`) into that row of each block, and each 16 bytes are XORed into the
  data through `xmm6` if they all lie within the data; the 16 bytes that
  run past its end, if any, are stored in `buf[0, 16)` (whose slot has been
  read), and their first bytes XORed into the data afterwards (`last`).

`vg_chacha20_xor_ssse3` (`xorSsse3`) is the same code with `vqr3` for `vqr`,
whose rotations by 16 and 8 bits are `pshufb`: the prologue stores its
controls in `buf[288, 320)` (`masks`), which nothing else writes.

If 64 bytes or fewer remain after that, `vg_chacha20_block(state, buf)` is
called and the first bytes of its output (the first 64 bytes of `buf`) are
XORed into the data (`tail`), 16 at a time through `xmm4` and `xmm5`, then
one at a time.

Across the calls, `ebx` holds `state`, `esi` the data not yet processed,
`edi` `buf` and `ebp` the number of bytes left: the block function preserves
them (it is cdecl). Our caller's values of those registers are saved in
`buf[256, 272)`, which is not passed to the block function. The call
pushes its two arguments (`buf`, then `state`) in a frame of its own, popped
(into `eax`) when it returns: with the return address the call stores, it
uses the 12 bytes below `esp`.

In the byte loop, `edx` points at the next byte of keystream and `ecx`
counts the bytes left; the data byte is XORed with the (little-endian) word
at `edx`, whose low byte is that keystream byte (the word lies within
`buf`).

The branches are on the length only, and every address is `esp`, a pointer
plus a constant or a pointer plus a count, so only the pointers and the length can affect
timing. On return `eax` holds `buf`.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86.Xor

open VG.X86
open VG.Impl.ChaCha20.X86 (at_ block xb vqr vqr3 masks)

/-- Our caller's callee-saved registers, and where they are saved in `buf`. -/
def saved : List (Reg × Nat) := [(.ebx, 256), (.esi, 260), (.edi, 264), (.ebp, 268)]

/-- Save them, with `buf` in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with `buf` in `eax`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- With `buf` in `eax`: save our caller's registers, and load the other
arguments. -/
def prologue : List Instr :=
  save ++ ([.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8)),
    .mov .ebp (.mem (at_ .esp 12))] : List Instr)

/-- `vg_chacha20_block(state, buf)`: the keystream block into `buf`. -/
def callBlock : Prog isa :=
  .frame (.push [.edi, .ebx]) (.call "vg_chacha20_block" block) (.pop .eax 2)

/-! ## XORing keystream into the data -/

/-- One byte: the data byte at `esi`, XORed with the keystream byte at `edx`. -/
def xorBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .xor .eax (.mem (at_ .edx 0)), .store8 (at_ .esi 0) .al,
   .alu .add .esi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- XORs the first `ecx` bytes of the keystream into the data (`ecx > 0`). -/
def xorLoop : Prog isa := .loop (.block xorBody) .ne

/-- XORs the `ecx` bytes at `edx` into the data (`esi`), advancing both. -/
def xorBytes : Prog isa :=
  .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) xorLoop)

/-- 16 bytes: the data at `esi`, XORed with the keystream at `edx`, through
`xmm4` and `xmm5`; then `CF` is clear if at least 16 bytes remain. -/
def chunkBody : List Instr :=
  [.movdquLoad .xmm4 (at_ .esi 0), .movdquLoad .xmm5 (at_ .edx 0), xb .pxor .xmm4 .xmm5,
   .movdquStore (at_ .esi 0) .xmm4, .alu .add .esi (.imm 16), .alu .add .edx (.imm 16),
   .alu .sub .ecx (.imm 16), .alu .cmp .ecx (.imm 16)]

/-- XORs the `ecx` bytes at `edx` into the data (`esi`), 16 at a time and then
one at a time, advancing both. -/
def xorWide : Prog isa :=
  .seq (.block [.alu .cmp .ecx (.imm 16)])
  (.seq (.ite .b (.block []) (.loop (.block chunkBody) .ae)) xorBytes)

/-- The last bytes (`0 < ebp ≤ 64`): the block of keystream into `buf`, and
its first `ebp` bytes XORed into the data. -/
def tail : Prog isa :=
  .seq callBlock (.seq (.block [.mov .edx (.reg .edi), .mov .ecx (.reg .ebp)]) xorWide)

/-! ## Four blocks at once, with SSE2 -/

/-- Where word `k` of the four states is kept, doubleword `l` for block `l`. -/
def slot (k : Nat) : Nat := 16 * k

/-- Where the four block counters are kept for the final addition. -/
def ctrOff : Nat := 272

/-- A quarter round of the rounds on the four states: the words loaded from
their slots first (into which register), the registers holding its words
`x, y, z, w` (RFC 8439 §2.2), and the words stored to their slots afterwards
(from which register). -/
structure QStep where
  loads : List (XReg × Nat)
  a : XReg
  b : XReg
  c : XReg
  d : XReg
  stores : List (Nat × XReg)

/-- Load word `k` from its slot into `r`. -/
def ld (r : XReg) (k : Nat) : Instr := .movdquLoad r (at_ .edi (slot k))

/-- Store word `k` from `r` into its slot. -/
def st (k : Nat) (r : XReg) : Instr := .movdquStore (at_ .edi (slot k)) r

/-- The quarter round of the four-block code (`vqr`, or `vqr3` with SSSE3),
and what the prologue does first for it (`vqr3`'s controls). -/
structure Kernel where
  qr : XReg → XReg → XReg → XReg → List Instr
  init : List Instr

def sse2 : Kernel := ⟨vqr, []⟩
def ssse3 : Kernel := ⟨vqr3, masks⟩

def QStep.code (k : Kernel) (q : QStep) : List Instr :=
  q.loads.map (fun p => ld p.1 p.2) ++ k.qr q.a q.b q.c q.d ++ q.stores.map fun p => st p.1 p.2

/-- The words kept in registers between double rounds. -/
def cached : List (Nat × XReg) :=
  [(0, .xmm0), (3, .xmm1), (4, .xmm2), (8, .xmm4), (9, .xmm3), (12, .xmm6), (14, .xmm5)]

/-- The quarter rounds of a double round, `QUARTERROUND(0, 4, 8, 12)`, …,
`QUARTERROUND(3, 4, 9, 14)`, with the words in registers: of the 32 words
that the quarter rounds of a double round use, 14 are in registers already
(the most that seven registers allow, for any order of the quarter rounds). -/
def plan : List QStep := [
  ⟨[], .xmm0, .xmm2, .xmm4, .xmm6, [(4, .xmm2), (8, .xmm4), (12, .xmm6)]⟩,
  ⟨[(.xmm2, 1), (.xmm4, 5), (.xmm6, 13)], .xmm2, .xmm4, .xmm3, .xmm6, [(1, .xmm2), (9, .xmm3), (13, .xmm6)]⟩,
  ⟨[(.xmm2, 2), (.xmm3, 6), (.xmm6, 10)], .xmm2, .xmm3, .xmm6, .xmm5, [(2, .xmm2), (6, .xmm3), (14, .xmm5)]⟩,
  ⟨[(.xmm2, 7), (.xmm3, 11), (.xmm5, 15)], .xmm1, .xmm2, .xmm3, .xmm5, []⟩,
  ⟨[], .xmm0, .xmm4, .xmm6, .xmm5, [(5, .xmm4), (10, .xmm6), (15, .xmm5)]⟩,
  ⟨[(.xmm4, 1), (.xmm5, 6), (.xmm6, 12)], .xmm4, .xmm5, .xmm3, .xmm6, [(1, .xmm4), (6, .xmm5), (11, .xmm3)]⟩,
  ⟨[(.xmm3, 2), (.xmm4, 8), (.xmm5, 13)], .xmm3, .xmm2, .xmm4, .xmm5, [(2, .xmm3), (7, .xmm2), (13, .xmm5)]⟩,
  ⟨[(.xmm2, 4), (.xmm3, 9), (.xmm5, 14)], .xmm1, .xmm2, .xmm3, .xmm5, []⟩]

/-- Quarter round `i` of `plan`. -/
def quarter4 (k : Kernel) (i : Nat) : Prog isa :=
  .block ((plan.getD i ⟨[], .xmm0, .xmm0, .xmm0, .xmm0, []⟩).code k)

/-- `inner_block` (RFC 8439 §2.3.1) on each of the four states. -/
def doubleRound4 (k : Kernel) : Prog isa :=
  .seq (quarter4 k 0) <| .seq (quarter4 k 1) <| .seq (quarter4 k 2) <| .seq (quarter4 k 3) <|
  .seq (quarter4 k 4) <| .seq (quarter4 k 5) <| .seq (quarter4 k 6) (quarter4 k 7)

/-- `n` double rounds on each of the four states. -/
def rounds4 (k : Kernel) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds4 k n) (doubleRound4 k)

/-- The rounds: the cached words loaded, ten double rounds, and the cached
words stored back. -/
def rounds10 (k : Kernel) : Prog isa :=
  .seq (.block (cached.map fun p => ld p.2 p.1))
  (.seq (rounds4 k 10) (.block (cached.map fun p => st p.1 p.2)))

/-- `pshufd` with `0x55 * i`: doubleword `i` of `src` in every doubleword of `d`. -/
def bcast (d src : XReg) (i : Nat) : Instr := .xop (.pshufd d src (BitVec.ofNat 8 (0x55 * i)))

/-- The registers `xmm0, …, xmm3`. -/
def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

/-- Row `r` of the state, each of its words in every doubleword of its slot. -/
def setupRow (r : Nat) : List Instr :=
  .movdquLoad .xmm4 (at_ .ebx (16 * r)) :: (List.range 4).flatMap fun i =>
    [bcast .xmm0 .xmm4 i, .movdquStore (at_ .edi (slot (4 * r + i))) .xmm0]

/-- Counter `c + l` (with `c + l` in `eax`) in doubleword `l` of the slot of
word 12 and of the counters at `ctrOff`; then `c + l + 1` into `eax`. -/
def ctrLane (l : Nat) : List Instr :=
  [.store (at_ .edi (slot 12 + 4 * l)) .eax, .store (at_ .edi (ctrOff + 4 * l)) .eax,
   .alu .add .eax (.imm 1)]

/-- The counters `c, c + 1, c + 2, c + 3` (from word 12 of the state) in the
slot of word 12 and at `ctrOff`. -/
def setupCtr : List Instr := .mov .eax (.mem (at_ .ebx 48)) :: (List.range 4).flatMap ctrLane

/-- The four states in their slots. -/
def setup4 : List Instr := (List.range 4).flatMap setupRow ++ setupCtr

/-- Words `4 r, …, 4 r + 3` of the four states into `xmm0, …, xmm3`, and row
`r` of the state into `xmm4`. -/
def loadRow (r : Nat) : List Instr :=
  [.movdquLoad .xmm0 (at_ .edi (slot (4 * r))), .movdquLoad .xmm1 (at_ .edi (slot (4 * r + 1))),
   .movdquLoad .xmm2 (at_ .edi (slot (4 * r + 2))), .movdquLoad .xmm3 (at_ .edi (slot (4 * r + 3))),
   .movdquLoad .xmm4 (at_ .ebx (16 * r))]

/-- Word `4 r + i` of the input states added to `xr i`, through `xmm5`:
row `r` of the state is in `xmm4`, and the counters at `ctrOff`. -/
def addWord4 (r i : Nat) : List Instr :=
  (if r = 3 ∧ i = 0 then .movdquLoad .xmm5 (at_ .edi ctrOff) else bcast .xmm5 .xmm4 i) ::
    [xb .paddd (xr i) .xmm5]

/-- Transpose the doublewords of `xmm0, …, xmm3` (doubleword `l` of `xr i`
being word `4 r + i` of block `l`), through `xmm4` and `xmm5`: afterwards
`xmm1, xmm4, xmm3, xmm0` hold row `r` of blocks 0, 1, 2, 3. -/
def transpose : List Instr :=
  [xb .movdqa .xmm4 .xmm0, xb .punpckldq .xmm4 .xmm1, xb .punpckhdq .xmm0 .xmm1,
   xb .movdqa .xmm5 .xmm2, xb .punpckldq .xmm5 .xmm3, xb .punpckhdq .xmm2 .xmm3,
   xb .movdqa .xmm1 .xmm4, xb .punpcklqdq .xmm1 .xmm5, xb .punpckhqdq .xmm4 .xmm5,
   xb .movdqa .xmm3 .xmm0, xb .punpcklqdq .xmm3 .xmm2, xb .punpckhqdq .xmm0 .xmm2]

/-- The register holding row `r` of block `l` after `transpose`. -/
def outReg : Nat → XReg
  | 0 => .xmm1 | 1 => .xmm4 | 2 => .xmm3 | _ => .xmm0

/-- The 16 bytes of `x` XORed into the data at `esi + off`, through `xmm6`. -/
def xor16 (x : XReg) (off : Nat) : List Instr :=
  [.movdquLoad .xmm6 (at_ .esi off), xb .pxor .xmm6 x, .movdquStore (at_ .esi off) .xmm6]

/-- The 16 bytes of keystream in `x`, for the data at offset `off`: XORed
into the data if it has at least `off + 16` bytes (`ebp`), stored in
`buf[0, 16)` if it has more than `off`, and dropped otherwise. -/
def chunk (x : XReg) (off : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .ebp (.imm (BitVec.ofNat 32 (off + 16)))])
    (.ite .b
      (.seq (.block [.alu .cmp .ebp (.imm (BitVec.ofNat 32 (off + 1)))])
        (.ite .b (.block []) (.block [.movdquStore (at_ .edi 0) x])))
      (.block (xor16 x off)))

/-- Where row `r` of block `l` goes in the data. -/
def chunkOff (r l : Nat) : Nat := 64 * l + 16 * r

/-- Row `r` of the four blocks of keystream (the rounds' result plus the
input states), for the next 256 bytes of data. -/
def finishRow (r : Nat) : Prog isa :=
  .seq (.block (loadRow r ++ ((List.range 4).flatMap (addWord4 r) ++ transpose)))
  (.seq (chunk (outReg 0) (chunkOff r 0)) (.seq (chunk (outReg 1) (chunkOff r 1))
  (.seq (chunk (outReg 2) (chunkOff r 2)) (chunk (outReg 3) (chunkOff r 3)))))

def finish4 : Prog isa :=
  .seq (finishRow 0) (.seq (finishRow 1) (.seq (finishRow 2) (finishRow 3)))

/-- At most 256 bytes were left (`ebp`): the first `ebp % 16` bytes of
`buf[0, 16)` XORed into the data that follows the multiple of 16, and no
bytes left. -/
def last : Prog isa :=
  .seq (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 15), .alu .and .ebp (.imm 0xfffffff0),
    .alu .add .esi (.reg .ebp), .mov .edx (.reg .edi), .mov .ebp (.imm 0)]) xorBytes

/-- More than 256 bytes were left: advance the counter by 4 and the data by
256 bytes. -/
def next4 : List Instr :=
  [.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 4), .store (at_ .ebx 48) .eax,
   .alu .add .esi (.imm 256), .alu .sub .ebp (.imm 256)]

/-- Four blocks of keystream, XORed into the next 256 bytes of data, or all
that is left if fewer; then `CF` is clear if more than 64 bytes remain. -/
def body4 (k : Kernel) : Prog isa :=
  .seq (.block setup4) (.seq (rounds10 k) (.seq finish4
  (.seq (.block [.alu .cmp .ebp (.imm 257)]) (.seq (.ite .b last (.block next4))
    (.block [.alu .cmp .ebp (.imm 65)])))))

def xorWith (k : Kernel) : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 16))])
  (.seq (.block prologue) (.seq (.block k.init) (.seq (.block [.alu .cmp .ebp (.imm 65)])
  (.seq (.ite .b (.block []) (.loop (body4 k) .ae))
  (.seq (.block [.alu .test .ebp (.reg .ebp)])
  (.seq (.ite .e (.block []) tail)
    (.block (.mov .eax (.reg .edi) :: restore))))))))

/-- `vg_chacha20_xor`. -/
def xor : Prog isa := xorWith sse2

/-- `vg_chacha20_xor_ssse3`. -/
def xorSsse3 : Prog isa := xorWith ssse3

end VG.Impl.ChaCha20.X86.Xor
