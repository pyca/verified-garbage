import VerifiedGarbage.Impl.ChaCha20.X86

/-!
# ChaCha20 keystream XOR: x86 (32-bit) implementation

`vg_chacha20_xor(state, data, len, buf)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

While at least 256 bytes remain, four blocks of keystream (the counters
`c, c + 1, c + 2, c + 3` modulo 2³², `c` being word 12 of the state) are
computed at once with SSE2 and XORed into the next 256 bytes, and word 12 of
the state is advanced by 4 (`body4`):

* Word `k` of the four states is kept in its slot, `buf[16 k, 16 k + 16)`,
  doubleword `l` for block `l`: each row of the state is broadcast from
  `state` with `pshufd`, and the four counters, computed in `eax`, are
  written to the slot of word 12 and to `buf[272, 288)`.
* Each quarter round loads its four slots into `xmm0, …, xmm3`, runs `vqr`
  (the quarter round on each doubleword, through `xmm4`) and stores them
  back; the ten double rounds are unrolled.
* At the end, each row of the four states is loaded, the input states are
  added (their rows broadcast again from `state`, through `xmm4` and
  `xmm5`, and the counters reloaded from `buf[272, 288)`), the four
  registers are transposed (`punpck{l,h}{dq,qdq}`, through `xmm4` and
  `xmm5`) into that row of each block, and each 16 bytes are XORed into the
  data through `xmm6`.

Then, for each 64 bytes of data left (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed into the data a
byte at a time, and the block counter (word 12 of the state) is incremented
modulo 2³².

Across the calls, `ebx` holds `state`, `esi` the data not yet processed,
`edi` `buf` and `ebp` the number of bytes left: the block function preserves
them (it is cdecl). Our caller's values of those registers are saved in
`buf[256, 272)`, which is not passed to the block function. Each call pushes
its two arguments (`buf`, then `state`) in a frame of its own, popped (into
`eax`) when it returns: with the return address the call stores, it uses the
12 bytes below `esp`.

In the byte loop, `edx` points at the next byte of keystream and `ecx`
counts the bytes left; the data byte is XORed with the (little-endian) word
at `edx`, whose low byte is that keystream byte (the word lies within
`buf`). Afterwards `edx - edi` is the number of bytes done.

The branches are on the length only, and every address is `esp`, a pointer
plus a constant or a pointer plus a count, so only the pointers and the length can affect
timing. On return `eax` holds `buf`.
-/

namespace VG.Impl.ChaCha20.X86.Xor

open VG.X86
open VG.Impl.ChaCha20.X86 (at_ block xb vqr)

/-- Our caller's callee-saved registers, and where they are saved in `buf`. -/
def saved : List (Reg × Nat) := [(.ebx, 256), (.esi, 260), (.edi, 264), (.ebp, 268)]

/-- Save them, with `buf` in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with `buf` in `eax`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- With `buf` in `eax`: save our caller's registers, load the other
arguments, and compare the length with 256. -/
def prologue : List Instr :=
  save ++ [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8)),
    .mov .ebp (.mem (at_ .esp 12)), .alu .cmp .ebp (.imm 256)]

/-- `vg_chacha20_block(state, buf)`: the keystream block into `buf`. -/
def callBlock : Prog isa :=
  .frame (.push [.edi, .ebx]) (.call "vg_chacha20_block" block) (.pop .eax 2)

/-- One byte: the data byte at `esi`, XORed with the keystream byte at `edx`. -/
def xorBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .xor .eax (.mem (at_ .edx 0)), .store8 (at_ .esi 0) .al,
   .alu .add .esi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- XORs the first `ecx` bytes of the keystream into the data. -/
def xorLoop : Prog isa := .loop (.block xorBody) .ne

/-- `ecx = min(64, ebp)`, and `edx` at the keystream. -/
def select : Prog isa :=
  .seq (.block [.mov .ecx (.reg .ebp), .alu .cmp .ebp (.imm 64)])
  (.seq (.ite .b (.block []) (.block [.mov .ecx (.imm 64)])) (.block [.mov .edx (.reg .edi)]))

/-- Increment the counter, and subtract the bytes done from those left. -/
def next : List Instr :=
  [.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1), .store (at_ .ebx 48) .eax,
   .alu .sub .edx (.reg .edi), .alu .sub .ebp (.reg .edx)]

/-- One block of keystream, XORed into up to 64 bytes of data. -/
def body : Prog isa := .seq callBlock (.seq select (.seq xorLoop (.block next)))

/-! ## Four blocks at once, with SSE2 -/

/-- Where word `k` of the four states is kept, doubleword `l` for block `l`. -/
def slot (k : Nat) : Nat := 16 * k

/-- Where the four block counters are kept for the final addition. -/
def ctrOff : Nat := 272

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2) on each of the four states. -/
def quarter4 (x y z w : Nat) : Prog isa := .block (
  [.movdquLoad .xmm0 (at_ .edi (slot x)), .movdquLoad .xmm1 (at_ .edi (slot y)),
   .movdquLoad .xmm2 (at_ .edi (slot z)), .movdquLoad .xmm3 (at_ .edi (slot w))] ++ vqr ++
  [.movdquStore (at_ .edi (slot x)) .xmm0, .movdquStore (at_ .edi (slot y)) .xmm1,
   .movdquStore (at_ .edi (slot z)) .xmm2, .movdquStore (at_ .edi (slot w)) .xmm3])

/-- `inner_block` (RFC 8439 §2.3.1) on each of the four states. -/
def doubleRound4 : Prog isa :=
  .seq (quarter4 0 4 8 12) <| .seq (quarter4 1 5 9 13) <| .seq (quarter4 2 6 10 14) <|
  .seq (quarter4 3 7 11 15) <| .seq (quarter4 0 5 10 15) <| .seq (quarter4 1 6 11 12) <|
  .seq (quarter4 2 7 8 13) (quarter4 3 4 9 14)

/-- `n` double rounds on each of the four states. -/
def rounds4 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds4 n) doubleRound4

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

/-- Row `r` of the four blocks of keystream (the rounds' result plus the
input states) XORed into the next 256 bytes of data. -/
def finishRow (r : Nat) : List Instr :=
  loadRow r ++ ((List.range 4).flatMap (addWord4 r) ++ (transpose ++
    (List.range 4).flatMap fun l => xor16 (outReg l) (64 * l + 16 * r)))

def finish4 : List Instr := (List.range 4).flatMap finishRow

/-- Advance the counter by 4 and the data by 256 bytes; `CF` is clear if at
least 256 bytes remain. -/
def next4 : List Instr :=
  [.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 4), .store (at_ .ebx 48) .eax,
   .alu .add .esi (.imm 256), .alu .sub .ebp (.imm 256), .alu .cmp .ebp (.imm 256)]

/-- Four blocks of keystream, XORed into the next 256 bytes of data. -/
def body4 : Prog isa := .seq (.block setup4) (.seq (rounds4 10) (.block (finish4 ++ next4)))

def xor : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 16))])
  (.seq (.block prologue)
  (.seq (.ite .b (.block []) (.loop body4 .ae))
  (.seq (.block [.alu .test .ebp (.reg .ebp)])
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (.mov .eax (.reg .edi) :: restore))))))

end VG.Impl.ChaCha20.X86.Xor
