module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor

/-!
# ChaCha20 keystream XOR: x86-64 implementation with SSSE3

`vg_chacha20_xor_ssse3(state = rdi, src = rsi, len = rdx, buf = rcx, dst = r8)`,
with the contract of `vg_chacha20_xor`, for CPUs with SSSE3. On entry
`r11` is set to `dst - src`, which nothing writes again: the destination of
the source byte at `rsi + d` is at `rsi + r11 + d`.

While more than 64 bytes remain, four blocks of keystream (the counters
`c, c + 1, c + 2, c + 3` modulo 2³², `c` being word 12 of the state) are
computed at once and XORed into the next 256 bytes, or into all that remain
if fewer (`body4`), as `vg_chacha20_xor` does on x86 (32-bit):

* Word `k` of the four states is kept in its slot, `buf[16 k, 16 k + 16)`,
  doubleword `l` for block `l`, or in an XMM register: each row of the
  state is broadcast from `state` with `pshufd` into the slots, and the four
  counters, computed in `eax`, are written to the slot of word 12 and to
  `buf[256, 272)`.
* The rounds keep fifteen of the sixteen words in `xmm0, …, xmm14`
  (`cached`, loaded from their slots first and stored back at the end): word
  15 is in its slot, but for the quarter rounds that use it
  (`QUARTERROUND(3, 7, 11, 15)` and `QUARTERROUND(0, 5, 10, 15)`), during
  which word 4, which neither uses, is in its slot in its place (`plan`). A
  double round then loads and stores two words. Each quarter round (`vqr`)
  goes through `xmm15`: its rotations by 16 and 8 bits are `pshufb` with the
  controls the prologue stores in `buf[272, 304)` (`masks`), which nothing
  else writes, loaded into `xmm15`; those by 12 and 7 two shifts and a `por`.
  The ten double rounds are unrolled.
* At the end, each row of the four states is loaded, the input states are
  added (their rows broadcast again from `state`, through `xmm4` and
  `xmm5`, and the counters reloaded from `buf[256, 272)`), the four
  registers are transposed (`punpck{l,h}{dq,qdq}`, through `xmm4` and
  `xmm5`) into that row of each block, and each 16 bytes of the source are
  XORed with them through `xmm6`, and stored to the destination, if they all
  lie within the data; the 16 bytes that run past its end, if any, are
  stored in `buf[0, 16)` (whose slot has been read), and XORed with the
  source's last bytes afterwards (`last`, by `XorBuf.xorBufTo`, with `buf`
  in `r9` and the destination in `r10`).

If 64 bytes or fewer remain after that, but some, `vg_chacha20_xor` XORs
them (from `rsi` to `rsi + r11`), and returns with `rsi` pointing at `buf`;
otherwise `rsi` is set to `buf`.

No callee-saved register is written: `state`, the source not yet
processed, the number of bytes left and `buf` stay in `rdi`, `rsi`, `rdx`
and `rcx` (but in `last`, where `buf` is in `r9`).

The branches are on the length only, and every address is a pointer plus a
constant or a count, so only the pointers and the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.Ssse3

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- `op dst, src` on XMM registers. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-! ## The quarter round on four blocks at once -/

/-- Where the `pshufb` controls are in `buf` (through `rcx`). -/
def rot16Off : Nat := 272
def rot8Off : Nat := 288

/-- The `pshufb` controls that rotate each doubleword left by 16 and by 8
bits (byte `j` of a doubleword from byte `(j + 2) % 4`, resp. `(j + 3) % 4`),
as the quadwords stored at `buf + rot16Off`. -/
def maskQ : List (BitVec 64) :=
  [0x0504070601000302, 0x0d0c0f0e09080b0a, 0x0605040702010003, 0x0e0d0c0f0a09080b]

/-- `x` rotated left by `k` (`0 < k < 32`) in each doubleword, through `xmm15`. -/
def vrot (x : XReg) (k : Nat) : List Instr :=
  [xb .movdqa .xmm15 x, .xop (.shift .pslld x (BitVec.ofNat 8 k)),
   .xop (.shift .psrld .xmm15 (BitVec.ofNat 8 (32 - k))), xb .por x .xmm15]

/-- The quarter round (RFC 8439 §2.1) on each doubleword of `a, b, c, d`,
with `xmm15` as scratch: the rotations by 16 and 8 are `pshufb` with the
controls at `buf + rot16Off` and `buf + rot8Off`, loaded into `xmm15`; the
others are two shifts and an `or`. -/
def vqr (a b c d : XReg) : List Instr :=
  [xb .paddd a b, xb .pxor d a, .movdquLoad .xmm15 (at_ .rcx rot16Off), xb .pshufb d .xmm15,
   xb .paddd c d, xb .pxor b c] ++ vrot b 12 ++
  [xb .paddd a b, xb .pxor d a, .movdquLoad .xmm15 (at_ .rcx rot8Off), xb .pshufb d .xmm15,
   xb .paddd c d, xb .pxor b c] ++ vrot b 7

/-- Store the quadwords `qs` at `buf + off` (`buf` in `rcx`), through `rax`. -/
def storeQ (off : Nat) (qs : List (BitVec 64)) : List Instr :=
  (List.range qs.length).flatMap fun i =>
    [.movImm64 .rax (qs.getD i 0), .store (at_ .rcx (off + 8 * i)) .rax]

/-- Stores the controls of `vqr` in `buf`. -/
def masks : List Instr := storeQ rot16Off maskQ

/-! ## The rounds -/

/-- Where word `k` of the four states is kept, doubleword `l` for block `l`. -/
def slot (k : Nat) : Nat := 16 * k

/-- Where the four block counters are kept for the final addition. -/
def ctrOff : Nat := 256

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
def ld (r : XReg) (k : Nat) : Instr := .movdquLoad r (at_ .rcx (slot k))

/-- Store word `k` from `r` into its slot. -/
def st (k : Nat) (r : XReg) : Instr := .movdquStore (at_ .rcx (slot k)) r

def QStep.code (q : QStep) : List Instr :=
  q.loads.map (fun p => ld p.1 p.2) ++ vqr q.a q.b q.c q.d ++ q.stores.map fun p => st p.1 p.2

/-- The words kept in registers between double rounds: word `k` in `xmm k`. -/
def cached : List (Nat × XReg) :=
  [(0, .xmm0), (1, .xmm1), (2, .xmm2), (3, .xmm3), (4, .xmm4), (5, .xmm5), (6, .xmm6),
   (7, .xmm7), (8, .xmm8), (9, .xmm9), (10, .xmm10), (11, .xmm11), (12, .xmm12), (13, .xmm13),
   (14, .xmm14)]

/-- The quarter rounds of a double round, `QUARTERROUND(0, 4, 8, 12)`, …,
`QUARTERROUND(3, 4, 9, 14)`, with the words in registers: word 15 takes
word 4's register from the third quarter round to the seventh. -/
def plan : List QStep := [
  ⟨[], .xmm0, .xmm4, .xmm8, .xmm12, []⟩,
  ⟨[], .xmm1, .xmm5, .xmm9, .xmm13, []⟩,
  ⟨[], .xmm2, .xmm6, .xmm10, .xmm14, [(4, .xmm4)]⟩,
  ⟨[(.xmm4, 15)], .xmm3, .xmm7, .xmm11, .xmm4, []⟩,
  ⟨[], .xmm0, .xmm5, .xmm10, .xmm4, []⟩,
  ⟨[], .xmm1, .xmm6, .xmm11, .xmm12, []⟩,
  ⟨[], .xmm2, .xmm7, .xmm8, .xmm13, [(15, .xmm4)]⟩,
  ⟨[(.xmm4, 4)], .xmm3, .xmm4, .xmm9, .xmm14, []⟩]

/-- Quarter round `i` of `plan`. -/
def quarter4 (i : Nat) : Prog isa :=
  .block ((plan.getD i ⟨[], .xmm0, .xmm0, .xmm0, .xmm0, []⟩).code)

/-- `inner_block` (RFC 8439 §2.3.1) on each of the four states. -/
def doubleRound4 : Prog isa :=
  .seq (quarter4 0) <| .seq (quarter4 1) <| .seq (quarter4 2) <| .seq (quarter4 3) <|
  .seq (quarter4 4) <| .seq (quarter4 5) <| .seq (quarter4 6) (quarter4 7)

/-- `n` double rounds on each of the four states. -/
def rounds4 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds4 n) doubleRound4

/-- The rounds: the cached words loaded, ten double rounds, and the cached
words stored back. -/
def rounds10 : Prog isa :=
  .seq (.block (cached.map fun p => ld p.2 p.1))
  (.seq (rounds4 10) (.block (cached.map fun p => st p.1 p.2)))

/-! ## The setup -/

/-- `pshufd` with `0x55 * i`: doubleword `i` of `src` in every doubleword of `d`. -/
def bcast (d src : XReg) (i : Nat) : Instr := .xop (.pshufd d src (BitVec.ofNat 8 (0x55 * i)))

/-- The registers `xmm0, …, xmm3`. -/
def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

/-- Row `r` of the state, each of its words in every doubleword of its slot. -/
def setupRow (r : Nat) : List Instr :=
  .movdquLoad .xmm4 (at_ .rdi (16 * r)) :: (List.range 4).flatMap fun i =>
    [bcast .xmm0 .xmm4 i, .movdquStore (at_ .rcx (slot (4 * r + i))) .xmm0]

/-- Counter `c + l` (with `c + l` in `eax`) in doubleword `l` of the slot of
word 12 and of the counters at `ctrOff`; then `c + l + 1` into `eax`. -/
def ctrLane (l : Nat) : List Instr :=
  [.store32 (at_ .rcx (slot 12 + 4 * l)) .rax, .store32 (at_ .rcx (ctrOff + 4 * l)) .rax,
   .alu32 .add .rax (.imm 1)]

/-- The counters `c, c + 1, c + 2, c + 3` (from word 12 of the state) in the
slot of word 12 and at `ctrOff`. -/
def setupCtr : List Instr := .mov32 .rax (.mem (at_ .rdi 48)) :: (List.range 4).flatMap ctrLane

/-- The four states in their slots. -/
def setup4 : List Instr := (List.range 4).flatMap setupRow ++ setupCtr

/-! ## The output -/

/-- Words `4 r, …, 4 r + 3` of the four states into `xmm0, …, xmm3`, and row
`r` of the state into `xmm4`. -/
def loadRow (r : Nat) : List Instr :=
  [.movdquLoad .xmm0 (at_ .rcx (slot (4 * r))), .movdquLoad .xmm1 (at_ .rcx (slot (4 * r + 1))),
   .movdquLoad .xmm2 (at_ .rcx (slot (4 * r + 2))), .movdquLoad .xmm3 (at_ .rcx (slot (4 * r + 3))),
   .movdquLoad .xmm4 (at_ .rdi (16 * r))]

/-- Word `4 r + i` of the input states added to `xr i`, through `xmm5`:
row `r` of the state is in `xmm4`, and the counters at `ctrOff`. -/
def addWord4 (r i : Nat) : List Instr :=
  (if r = 3 ∧ i = 0 then .movdquLoad .xmm5 (at_ .rcx ctrOff) else bcast .xmm5 .xmm4 i) ::
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

/-- The 16 bytes of the source at `rsi + off` XORed with `x`, through
`xmm6`, to the destination at `rsi + r11 + off`. -/
def xor16 (x : XReg) (off : Nat) : List Instr :=
  [.movdquLoad .xmm6 (at_ .rsi off), xb .pxor .xmm6 x, .movdquStore (XorBuf.atDst (some .r11) off) .xmm6]

/-- The 16 bytes of keystream in `x`, for the data at offset `off`: XORed
into the data if it has at least `off + 16` bytes (`rdx`), stored in
`buf[0, 16)` if it has more than `off`, and dropped otherwise. -/
def chunk (x : XReg) (off : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 (off + 16)))])
    (.ite .b
      (.seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 (off + 1)))])
        (.ite .b (.block []) (.block [.movdquStore (at_ .rcx 0) x])))
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

/-- At most 256 bytes were left (`rdx`): the first `rdx % 16` bytes of
`buf[0, 16)` XORed with the source's bytes that follow the multiple of 16,
to the destination's (with `buf` in `r9`, as `XorBuf.xorBufTo` writes
`rcx`, and the destination in `r10`), the source's pointer at its end, and
no bytes left. -/
def last : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rcx), .mov .rax (.reg .rdx), .alu .and .rax (.imm 0xfffffff0),
    .alu .add .rsi (.reg .rax), .alu .and .rdx (.imm 15), .mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi)])
  (.seq (XorBuf.xorBufTo .r10 .rsi .r9)
    (.block [.mov .rcx (.reg .r9), .alu .add .rsi (.reg .rdx), .mov32 .rdx (.imm 0)]))

/-- More than 256 bytes were left: advance the counter by 4 and the data by
256 bytes. -/
def next4 : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 4), .store32 (at_ .rdi 48) .rax,
   .alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)]

/-- Four blocks of keystream, XORed into the next 256 bytes of data, or all
that is left if fewer; then `CF` is clear if more than 64 bytes remain. -/
def body4 : Prog isa :=
  .seq (.block setup4) (.seq rounds10 (.seq finish4
  (.seq (.block [.alu .cmp .rdx (.imm 257)]) (.seq (.ite .b last (.block next4))
    (.block [.alu .cmp .rdx (.imm 65)])))))

/-- The last bytes (at most 64), by `vg_chacha20_xor`, which returns with
`rsi` pointing at `buf`; if there are none, `rsi` is set to `buf`. -/
def tail : Prog isa :=
  .seq (.block [.alu .test .rdx (.reg .rdx)])
    (.ite .e (.block [.mov .rsi (.reg .rcx)])
      (Xor.callTo "vg_chacha20_xor" Xor.xor))

/-- `vg_chacha20_xor_ssse3`. -/
def xor : Prog isa :=
  .seq (.block (masks ++ XorBuf.delta ++ ([.alu .cmp .rdx (.imm 65)] : List Instr)))
  (.seq (.ite .b (.block []) (.loop body4 .ae)) tail)

end VG.Impl.ChaCha20.X86_64.Ssse3
