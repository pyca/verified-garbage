module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# Poly1305: x86 (32-bit) implementation

Every argument is on the stack (cdecl): `[esp + 4]`, `[esp + 8]`, … on entry,
and no code here moves `esp`, so they stay there.

The arithmetic is in radix `2³²`, as in OpenSSL's 32-bit x86 code without
SSE2: the accumulator `h = h0 + 2³² h1 + 2⁶⁴ h2 + 2⁹⁶ h3 + 2¹²⁸ h4` is five
32-bit words, which are the words it is stored as, and the clamped `r = r0 +
2³² r1 + 2⁶⁴ r2 + 2⁹⁶ r3` four, with `rj < 2²⁸` and `r1, r2, r3` multiples
of 4. `mul` multiplies 32-bit words into 64 bits, so a product term `hi rj`
of weight `2^(32 (i + j))` with `i + j ≥ 4` and `j ≥ 1` is folded into weight
`2^(32 (i + j - 4))` as `hi sj`, where `sj = rj + rj / 4 = 5 rj / 4` (as
`2¹²⁸ rj = 2¹³⁰ (rj / 4) ≡ 5 (rj / 4)` modulo `p = 2¹³⁰ - 5`).

The state (`state`, 128 bytes, see `VG.Spec.Poly1305.Buffered`):

* `[0, 24)`: the accumulator: `h` in `[0, 20)`, fully reduced (`h < p`)
  between calls, and a word that is zero between calls and holds the saved
  `ebp` during one;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the buffer: the message's last bytes that do not fill a block,
  padded in place in `finalize`;
* `[72, 88)`: the clamped `r0, …, r3`, and `[88, 100)`: `s1, s2, s3`,
  computed on entry;
* `[100, 116)`: the low words of a product, and of `h + 5`;
* `[116, 128)`: the saved `ebx, esi, edi`.

`update` and `finalize` do not need their `scratch`.

`edi` holds `state`. A block (at `esi`, or the buffer) is added to `h` in
place; then each `dk = Σ hi · c(k, i)` (`c` being an `rj` or an `sj`) is
summed into `ebx` (low word) and `ebp`, starting from the carry out of
`d(k-1)`, one product `eax · ecx` at a time, and its low word stored.
`d4 = h4 r0` (plus the carry) fits a word; its bits from 2 up are folded,
times 5, into the bottom (`5 ⌊d4 / 4⌋`, which fits a word too). Between
blocks, `h4 ≤ 4`.

Before `h` is stored, it is reduced fully: `h + 5 - 2¹³⁰` (`h - p`) is
selected, with a mask and without a branch, if `h + 5 ≥ 2¹³⁰`.

The only branches are on the block count, `count mod 16` (the number of
bytes buffered) and the lengths, and every address is `esp`, a pointer or a
pointer plus a constant, a count or `count mod 16`, so only the pointers,
`count` and the lengths can affect timing.
-/

@[expose] public section

namespace VG.Impl.Poly1305.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## Offsets in the state -/

/-- `hi`, `rj`, `sj` and the low words `tk` of a product. -/
def hOff (i : Nat) : Nat := 4 * i
def rOff (j : Nat) : Nat := 72 + 4 * j
def sOff (j : Nat) : Nat := 84 + 4 * j
def tOff (k : Nat) : Nat := 100 + 4 * k
/-- Where the callee-saved registers are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 116), (.esi, 120), (.edi, 124), (.ebp, 20)]

/-! ## `init(state, key)` -/

def init : Prog isa := .block (
  ([.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8))] : List Instr) ++
  (List.range 8).flatMap (fun j => [.mov .edx (.mem (at_ .ecx (4 * j))), .store (at_ .eax (24 + 4 * j)) .edx]) ++
  ([.mov .edx (.imm 0)] : List Instr) ++ (List.range 6).map fun j => .store (at_ .eax (4 * j)) .edx)

/-! ## Common parts -/

/-- `state` into `edi`, saving `ebx, esi, edi, ebp` in it (via `eax`). -/
def save : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) :: saved.map (fun (r, d) => .store (at_ .eax d) r) ++ ([.mov .edi (.reg .eax)] : List Instr)

/-- Restore them (via `eax`, from `edi`), and zero the word that held `ebp`. -/
def restore : List Instr :=
  .mov .eax (.reg .edi) :: saved.map (fun (r, d) => .mov r (.mem (at_ .eax d))) ++
    ([.mov .ecx (.imm 0), .store (at_ .eax 20) .ecx] : List Instr)

/-- `r0` clamped. -/
def clamp0 : List Instr :=
  [.mov .eax (.mem (at_ .edi 24)), .alu .and .eax (.imm 0x0fffffff), .store (at_ .edi (rOff 0)) .eax]

/-- `rj` clamped and `sj = rj + rj / 4`, for `j = 1, 2, 3`. -/
def clampS (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (24 + 4 * j))), .alu .and .eax (.imm 0x0ffffffc),
    .store (at_ .edi (rOff j)) .eax, .mov .ecx (.reg .eax), .shift .shr .ecx 2,
    .alu .add .eax (.reg .ecx), .store (at_ .edi (sOff j)) .eax]

/-- Everything each function but `init` does first. -/
def setup : List Instr := save ++ clamp0 ++ clampS 1 ++ clampS 2 ++ clampS 3

/-! ## Absorbing a block -/

/-- Word `i` of `h` plus word `i` of the block at `b + d`, with the carry in
unless `i = 0`. -/
def addWord (b : Reg) (d i : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff i))), .alu (if i = 0 then .add else .adc) .eax (.mem (at_ b (d + 4 * i))),
    .store (at_ .edi (hOff i)) .eax]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`. -/
def addBlock (b : Reg) (d : Nat) (pad : BitVec 32) : List Instr :=
  addWord b d 0 ++ addWord b d 1 ++ addWord b d 2 ++ addWord b d 3 ++
  ([.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm pad), .store (at_ .edi (hOff 4)) .eax] : List Instr)

/-- `ebx:ebp += hi · c`, the coefficient `c` at `[edi + off]`. -/
def mac (i off : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff i))), .mov .ecx (.mem (at_ .edi off)), .mul .ecx,
    .alu .add .ebx (.reg .eax), .alu .adc .ebp (.reg .edx)]

/-- The offset of the coefficient of `hi` in `dk` (`k < 4`): `r(k-i)`, or
`s(k+4-i)`. -/
def coef (k i : Nat) : Nat := if i ≤ k then rOff (k - i) else sOff (k + 4 - i)

/-- The number of terms of `dk`: `h4 r0` is not folded into `d0`. -/
def nterms (k : Nat) : Nat := if k = 0 then 4 else 5

/-- `dk` (`k < 4`) added to `ebx:ebp`, its low word stored, and its high word
moved to `ebx` as the carry into `d(k+1)`. -/
def dsum (k : Nat) : List Instr :=
  (List.range (nterms k)).flatMap (fun i => mac i (coef k i)) ++
  ([.store (at_ .edi (tOff k)) .ebx, .mov .ebx (.reg .ebp), .mov .ebp (.imm 0)] : List Instr)

/-- `d0, …, d3`, then `d4 = h4 r0` plus the carry, in `ebx`. -/
def products : List Instr :=
  ([.mov .ebx (.imm 0), .mov .ebp (.imm 0)] : List Instr) ++ (List.range 4).flatMap dsum ++ mac 4 (rOff 0)

/-- `h = t0 + 2³² t1 + 2⁶⁴ t2 + 2⁹⁶ t3 + 2¹²⁸ (d4 mod 4) + 5 ⌊d4 / 4⌋`. -/
def carry : List Instr :=
  ([.mov .eax (.reg .ebx), .shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx), .alu .and .ebx (.imm 3),
    .alu .add .eax (.mem (at_ .edi (tOff 0))), .store (at_ .edi (hOff 0)) .eax] : List Instr) ++
  (List.range 3).flatMap (fun k => [.mov .eax (.mem (at_ .edi (tOff (k + 1)))), .alu .adc .eax (.imm 0),
    .store (at_ .edi (hOff (k + 1))) .eax]) ++
  ([.alu .adc .ebx (.imm 0), .store (at_ .edi (hOff 4)) .ebx] : List Instr)

/-- Absorbing the block at `b + d`, with `pad = 1` for a whole block (the
`0x01` byte appended to it is `2¹²⁸`) and `pad = 0` for a padded last block
(whose `0x01` byte is inside it). -/
def absorbAt (b : Reg) (d : Nat) (pad : BitVec 32) : List Instr := addBlock b d pad ++ products ++ carry

/-- Absorbing the block at `esi`. -/
def absorb (pad : BitVec 32) : List Instr := absorbAt .esi 0 pad

/-! ## The final reduction -/

/-- `g = h + 5`: its low words stored at `tOff`, its top word in `edx`, and
the mask `-⌊g / 2¹³⁰⌋` in `ebp`. -/
def plus5 : List Instr :=
  ([.mov .eax (.mem (at_ .edi (hOff 0))), .alu .add .eax (.imm 5), .store (at_ .edi (tOff 0)) .eax] : List Instr) ++
  (List.range 3).flatMap (fun k => [.mov .eax (.mem (at_ .edi (hOff (k + 1)))), .alu .adc .eax (.imm 0),
    .store (at_ .edi (tOff (k + 1))) .eax]) ++
  ([.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm 0), .mov .edx (.reg .eax),
    .shift .shr .eax 2, .mov .ebp (.imm 0), .alu .sub .ebp (.reg .eax)] : List Instr)

/-- Word `k < 4` of `h` replaced by that of `g` where the mask is set. -/
def selectWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff k))), .mov .ecx (.mem (at_ .edi (tOff k))), .alu .xor .ecx (.reg .eax),
    .alu .and .ecx (.reg .ebp), .alu .xor .eax (.reg .ecx), .store (at_ .edi (hOff k)) .eax]

/-- The top word: that of `g` minus 4 (`g - 2¹³⁰`), or that of `h`. -/
def selectTop : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff 4))), .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ebp),
    .alu .xor .eax (.reg .edx), .alu .and .eax (.imm 3), .store (at_ .edi (hOff 4)) .eax]

/-- `h` reduced fully, in place. -/
def reduce : List Instr :=
  plus5 ++ (List.range 4).flatMap selectWord ++ selectTop

/-! ## Sixteen blocks or more: two lanes in radix `2²⁶`, with SSE2

From 16 blocks on (`pairs`), the blocks are absorbed two at a time in the
two 64-bit lanes of `xmm0`, …, `xmm4`, which hold five limbs of 26 bits (and
a little more) of two numbers `A` (the low lanes) and `B`: with `h` the
accumulator before blocks `m₁, m₂, …`, the lanes start as `A = h + m₁`,
`B = m₂`, each further pair of blocks makes them `A r² + m`, `B r² + m'`,
and at the end `h` is `A r² + B r`. So after every pair `A r² + B r` is the
accumulator after the blocks so far.

`pmuludq` multiplies registers, and eight registers cannot hold the
multipliers, so they are in a frame of 512 bytes on the stack, 16 bytes
each (`slot`): the limbs of `r²` in both lanes and their multiples by 5
(table 0), the limbs of `r²` and of `r` and their multiples by 5 (table 1),
and the bit `2²⁴` of a block's fifth limb (`2¹²⁸`); the lanes themselves are
kept there too, between two multiplications (see "A turn of the loop").
`r²` is computed first, in `h`, by the code that absorbs a block (the block
`r` into `h = 0`, `h` being saved in the frame), and reduced fully; the
lanes take `h` from the frame, and `h` is written again at the end, from the
five limbs of the result, which the frame holds too, as it does the number
of pairs.

`pmuludq` runs inside an MCDT frame (`TCB/X86/Isa.lean`), where the frame
of 512 bytes is 12 bytes further up (`o = 12`). Before the frame is
released, it and the SSE registers are zeroed. The branches are on the
number of pairs, and every address is `esp`, `edi` or `esi` plus a
constant. -/

/-- `[esp + o + d]`: the byte `d` of the frame, `o` being 12 inside the MCDT
frame and 0 outside. -/
def fs (o d : Nat) : MemOp := at_ .esp (o + d)

/-- Where `h` is saved, and the number of pairs. -/
def svOff (k : Nat) : Nat := 4 * k
def cntOff : Nat := 20
/-- The 16-byte slot `j`. -/
def slot (j : Nat) : Nat := 64 + 16 * j
/-- Limb `k` of table `t`, and its multiple by 5. -/
def rSlot (t k : Nat) : Nat := slot (10 * t + k)
def sSlot (t k : Nat) : Nat := slot (10 * t + 5 + k)
def hibitSlot : Nat := slot 21
/-- Limb `k` of the result, 8 bytes. -/
def outOff (k : Nat) : Nat := 464 + 8 * k

/-- The register of limb `k`. -/
def lreg : Nat → XReg
  | 0 => .xmm0
  | 1 => .xmm1
  | 2 => .xmm2
  | 3 => .xmm3
  | _ => .xmm4

/-- Limb `k` of a block is its 8 bytes from byte `lbyte k` on, shifted right
by `lshift k` and masked. -/
def lbyte : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 6
  | _ => 8
def lshift : Nat → Nat
  | 0 => 0
  | 1 => 26
  | 2 => 4
  | 3 => 14
  | _ => 40

/-- The limbs of a fully reduced `h` (17 bytes and a little: less than
`2¹³⁰`): as a block's, but the fifth is the 26 bits from byte 13 on. -/
def qbyte : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 6
  | 3 => 8
  | _ => 13
def qshift : Nat → Nat
  | 0 => 0
  | 1 => 26
  | 2 => 4
  | 3 => 14
  | _ => 0

/-- The 8 bytes at `b + d`, shifted right by `n` and masked, into `xmm6` (low
lane; with `two`, the same of the 8 bytes at `b + d + 16` in the high lane,
through `xmm7`); `xmm5` holds the mask. -/
def limb (b : Reg) (d n : Nat) (two : Bool) : List Instr :=
  ([.movqLoad .xmm6 (at_ b d)] : List Instr) ++
  (if two then [.movqLoad .xmm7 (at_ b (d + 16)), .xop (.bin .punpcklqdq .xmm6 .xmm7)] else []) ++
  ([.xop (.shift .psrlq .xmm6 (BitVec.ofNat 8 n)), .xop (.bin .pand .xmm6 .xmm5)] : List Instr)

/-- The limbs of the two blocks at `esi`, with their `2¹²⁸`, added to the
lanes. -/
def addMsg (o : Nat) : List Instr :=
  ((List.range 5).flatMap fun k => limb .esi (lbyte k) (lshift k) true ++
    ([.xop (.bin .paddq (lreg k) .xmm6)] : List Instr)) ++
  ([.movdquLoad .xmm7 (fs o hibitSlot), .xop (.bin .paddq .xmm4 .xmm7)] : List Instr)

/-- The limbs of `h`, saved in the frame, into the low lanes; the high lanes
are zero. The fifth limb gets the top word, times `2²⁴` (through `eax`): its
low three bits, which are all of it in a state the contract describes (it is
at most 4), so that the lanes are bounded whatever the state holds. -/
def initH (o : Nat) : List Instr :=
  ((List.range 5).flatMap fun k => limb .esp (o + lbyte k) (lshift k) false ++
    ([.xop (.bin .movdqa (lreg k) .xmm6)] : List Instr)) ++
  ([.mov .eax (.mem (fs o (svOff 4))), .alu .and .eax (.imm 7), .xop (.movd .xmm6 .eax),
    .xop (.shift .psllq .xmm6 24), .xop (.bin .paddq .xmm4 .xmm6)] : List Instr)

/-- The mask in `xmm5`, for `tables`, `initH` and `addMsg`, and the bit
`2²⁴` in its slot, in both lanes. -/
def consts (o : Nat) : List Instr :=
  [.mov .eax (.imm 0x3ffffff), .xop (.movd .xmm5 .eax), .xop (.bin .punpcklqdq .xmm5 .xmm5),
   .mov .eax (.imm 0x1000000), .xop (.movd .xmm6 .eax), .xop (.bin .punpcklqdq .xmm6 .xmm6),
   .movdquStore (fs o hibitSlot) .xmm6]

/-- `x`, times 5, into the slot at `d` (through `xmm7`). -/
def times5 (o d : Nat) (x : XReg) : List Instr :=
  [.xop (.bin .movdqa .xmm7 x), .xop (.shift .psllq .xmm7 2), .xop (.bin .paddq .xmm7 x), .movdquStore (fs o d) .xmm7]

/-- Limb `k` of the tables: `h` holds `r²`, fully reduced (its limb in both
lanes of table 0, in the low lane of table 1), and `r` is at `edi + 72` (the
high lane of table 1). -/
def tableLimb (o k : Nat) : List Instr :=
  limb .edi (qbyte k) (qshift k) false ++ ([.xop (.bin .movdqa .xmm0 .xmm6)] : List Instr) ++
  limb .edi (rOff 0 + lbyte k) (lshift k) false ++
  ([.xop (.bin .movdqa .xmm1 .xmm0), .xop (.bin .punpcklqdq .xmm1 .xmm1), .movdquStore (fs o (rSlot 0 k)) .xmm1,
    .xop (.bin .punpcklqdq .xmm0 .xmm6), .movdquStore (fs o (rSlot 1 k)) .xmm0] : List Instr) ++
  times5 o (sSlot 0 k) .xmm1 ++ times5 o (sSlot 1 k) .xmm0

def tables (o : Nat) : List Instr := (List.range 5).flatMap (tableLimb o)

/-- The high lanes added to the low ones. -/
def sumLanes : List Instr :=
  (List.range 5).flatMap fun k => [.xop (.bin .movdqa .xmm6 (lreg k)), .xop (.shift .psrldq .xmm6 8),
    .xop (.bin .paddq (lreg k) .xmm6)]

/-- The low lanes into the frame. -/
def storeOut (o : Nat) : List Instr := (List.range 5).map fun k => .movqStore (fs o (outOff k)) (lreg k)

/-- `h` saved in the frame, and zeroed. -/
def saveH : List Instr :=
  ((List.range 5).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))), .store (fs 0 (svOff k)) .eax]) ++
  ([.mov .eax (.imm 0)] : List Instr) ++ (List.range 5).map fun k => .store (at_ .edi (hOff k)) .eax

/-- Limb `k + 1` of the number whose limbs are in the frame, times
`2^(26 − 6 k)` (so that it weighs `2^(32 k)`), added at word `k` of `h`: the
low word of the product completes the word in `ebx`, which is stored, and
the high word and the carry are the next. -/
def packStep (k : Nat) : List Instr :=
  [.mov .eax (.mem (fs 0 (outOff (k + 1)))), .mov .ecx (.imm (BitVec.ofNat 32 (2 ^ (26 - 6 * k)))), .mul .ecx,
    .alu .add .ebx (.reg .eax), .store (at_ .edi (hOff k)) .ebx, .alu .adc .edx (.imm 0), .mov .ebx (.reg .edx)]

/-- The number whose limbs `storeOut` left in the frame, into the words of `h`. -/
def packH : List Instr :=
  ([.mov .ebx (.mem (fs 0 (outOff 0)))] : List Instr) ++ (List.range 4).flatMap packStep ++
  ([.store (at_ .edi (hOff 4)) .ebx] : List Instr)

/-- The SSE registers and the frame zeroed. -/
def wipeV : List Instr :=
  ([.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7].map fun x => .xop (.bin .pxor x x)) ++
  (List.range 32).map fun j => .movdquStore (fs 0 (16 * j)) .xmm0

/-! ### A turn of the loop

A legacy SSE instruction that writes a whole register without reading it (a
load, `movdqa`) keeps the register's bits from 128 up. Where the processor
does not know them to be zero (on Zen 4, once any 256-bit instruction has
run in the process, until the kernel next restores the state), such a write
waits for the register's previous value: the products of a multiplication,
which are independent, then follow one another through every register they
share. So a multiplication spreads them over all eight registers
(`sumsOps`):

* the lanes are also kept in five slots of the frame (`hIdx`), stored at the
  end of a turn;
* the sum `d0` multiplies the lanes' registers themselves (`pmuludq h_i, c`:
  the other register only loads the multiplier), after which they are free;
* the other sums are computed two at a time (`d3` and `d1`, then `d4` and
  `d2`), sum `k` in `xmm<k>`: for each limb one register loads it from its
  slot, and two others load the multipliers;
* in a turn, the limbs of the next two blocks are added to the sums, not to
  the carried lanes, while registers are free: the lanes leave a turn
  carried;
* no register holds the mask in the carries: the low 26 bits of a lane are
  kept by two shifts.

The multiplication after the loop is the same, by table 1 and without
blocks. The sums and the carries are lists of operations on the lanes
(`LOp`), which `Proof/Poly1305/X86/Sse2.lean` evaluates. -/

/-- An operation of a turn: an SSE2 instruction (or two) on whole registers,
a slot of the frame or eight bytes of the data loaded. -/
inductive LOp
  /-- `movdqu x, [slot j]` -/
  | slot (x : XReg) (j : Nat)
  /-- `movq x, [esi + d]` -/
  | data (x : XReg) (d : Nat)
  /-- `pmuludq x, y` -/
  | mul (x y : XReg)
  /-- `paddq x, y` -/
  | add (x y : XReg)
  /-- `punpcklqdq x, y` -/
  | unpck (x y : XReg)
  /-- `movdqa x, y` -/
  | mov (x y : XReg)
  /-- `psrlq x, n` -/
  | shr (x : XReg) (n : Nat)
  /-- `psllq x, n` -/
  | shl (x : XReg) (n : Nat)
  /-- The 26 bits of each lane from bit `n` on: `psllq x, 38 - n; psrlq x, 38`. -/
  | bits (x : XReg) (n : Nat)
  /-- The low 26 bits of each lane: `psllq x, 38; psrlq x, 38`. -/
  | low26 (x : XReg)
  deriving DecidableEq, Repr

/-- The instructions of an operation, with the frame at `esp + o`. -/
def LOp.instrs (o : Nat) : LOp → List Instr
  | .slot x j => [.movdquLoad x (fs o (VG.Impl.Poly1305.X86.slot j))]
  | .data x d => [.movqLoad x (at_ .esi d)]
  | .mul x y => [.pmuludq x y]
  | .add x y => [.xop (.bin .paddq x y)]
  | .unpck x y => [.xop (.bin .punpcklqdq x y)]
  | .mov x y => [.xop (.bin .movdqa x y)]
  | .shr x n => [.xop (.shift .psrlq x (BitVec.ofNat 8 n))]
  | .shl x n => [.xop (.shift .psllq x (BitVec.ofNat 8 n))]
  | .bits x n => [.xop (.shift .psllq x (BitVec.ofNat 8 (38 - n))), .xop (.shift .psrlq x 38)]
  | .low26 x => [.xop (.shift .psllq x 38), .xop (.shift .psrlq x 38)]

/-- The index of the slot of the multiplier of limb `i` in the sum `dk`, in
table `t`: a limb of the multiplier, or five times one. -/
def mIdx (t k i : Nat) : Nat := if i ≤ k then 10 * t + (k - i) else 10 * t + 5 + (k + 5 - i)
/-- The index of the slot of limb `k` of the lanes. -/
def hIdx (k : Nat) : Nat := 22 + k

/-- The product of limb `i` for the sum `dk`, in the limb's own register
(through `c`). -/
def ownProd (t k i : Nat) (c : XReg) : List LOp := [.slot c (mIdx t k i), .mul (lreg i) c]

/-- The product of limb `i`, which `h` holds, for the sum `dk`, in `r`: it
starts the sum (`r` is then `xmm<k>`), or is added to it. -/
def prodOps (t k i : Nat) (h r : XReg) : List LOp :=
  ([.slot r (mIdx t k i), .mul r h] : List LOp) ++ (if i = 0 then [] else [.add (lreg k) r])

/-- Limb `k` of the two blocks at `esi` (through `x` and `y`), added to the
sum `dk`. -/
def limbOps (k : Nat) (x y : XReg) : List LOp :=
  [.data x (lbyte k), .data y (lbyte k + 16), .unpck x y, if k = 4 then .shr x 40 else .bits x (lshift k),
    .add (lreg k) x]

/-- The products of limb `i` for the sums `dk` and `dj`: `h` loads the limb. -/
def pairOps (t k j i : Nat) (h r r' : XReg) : List LOp :=
  ([.slot h (hIdx i)] : List LOp) ++ prodOps t k i h r ++ prodOps t j i h r'

/-- The five sums of products of the lanes with table `t`, sum `k` in
`xmm<k>`, with the limbs of the two blocks at `esi` and their `2¹²⁸` if
`msg`. The lanes are in their registers and in their slots. -/
def sumsOps (t : Nat) (msg : Bool) : List LOp :=
  ownProd t 0 0 .xmm6 ++ ownProd t 0 1 .xmm5 ++ ownProd t 0 2 .xmm7 ++ ownProd t 0 3 .xmm5 ++ ownProd t 0 4 .xmm6 ++
  ([.add .xmm0 .xmm1, .add .xmm0 .xmm2, .add .xmm0 .xmm3, .add .xmm0 .xmm4] : List LOp) ++
  (if msg then limbOps 0 .xmm7 .xmm5 else []) ++
  pairOps t 3 1 0 .xmm6 .xmm3 .xmm1 ++
  (if msg then limbOps 3 .xmm2 .xmm5 ++ limbOps 1 .xmm4 .xmm6 else []) ++
  pairOps t 3 1 1 .xmm5 .xmm6 .xmm7 ++ pairOps t 3 1 2 .xmm5 .xmm2 .xmm4 ++
  pairOps t 3 1 3 .xmm5 .xmm6 .xmm7 ++ pairOps t 3 1 4 .xmm5 .xmm2 .xmm4 ++
  pairOps t 4 2 0 .xmm5 .xmm4 .xmm2 ++
  (if msg then limbOps 4 .xmm5 .xmm6 ++ ([.slot .xmm7 21, .add .xmm4 .xmm7] : List LOp) ++ limbOps 2 .xmm6 .xmm7
    else []) ++
  pairOps t 4 2 1 .xmm5 .xmm7 .xmm6 ++ pairOps t 4 2 2 .xmm5 .xmm7 .xmm6 ++
  pairOps t 4 2 3 .xmm5 .xmm7 .xmm6 ++ pairOps t 4 2 4 .xmm5 .xmm7 .xmm6

/-- The bits of limb `i` from 26 up carried into limb `j` (times 5 from the
fifth limb into the first), through `x` (and `y`). -/
def cOps (x y : XReg) (i j : Nat) : List LOp :=
  ([.mov x (lreg i), .shr x 26, .low26 (lreg i)] : List LOp) ++
  (if i = 4 then [.mov y x, .shl y 2, .add x y] else []) ++ ([.add (lreg j) x] : List LOp)

/-- The carries: `d0 → d1`, `d3 → d4`, `d1 → d2`, `d4 → d0` (times 5),
`d2 → d3`, `d0 → d1`, `d3 → d4`. -/
def carryOps : List LOp :=
  cOps .xmm5 .xmm7 0 1 ++ cOps .xmm5 .xmm7 3 4 ++ cOps .xmm5 .xmm7 1 2 ++ cOps .xmm5 .xmm7 4 0 ++
  cOps .xmm6 .xmm7 2 3 ++ cOps .xmm7 .xmm5 0 1 ++ cOps .xmm5 .xmm7 3 4

/-- The lanes into their slots. -/
def storeH (o : Nat) : List Instr := (List.range 5).map fun k => .movdquStore (fs o (slot (hIdx k))) (lreg k)

/-- A turn of the loop: the lanes times `r²` plus the next two blocks,
carried, and stored. -/
def turn (o : Nat) : List Instr :=
  (sumsOps 0 true).flatMap (LOp.instrs o) ++ carryOps.flatMap (LOp.instrs o) ++ storeH o

/-- What the MCDT frame runs: the tables, the lanes from `h` and the first
two blocks, a pair of blocks at a time, and the result's limbs. -/
def lanes : Prog isa :=
  .seq (.block (consts 12 ++ tables 12 ++ initH 12 ++ addMsg 12 ++ storeH 12 ++
    ([.alu .add .esi (.imm 32), .mov .ecx (.mem (fs 12 cntOff)), .alu .sub .ecx (.imm 1)] : List Instr)))
  (.seq (.loop (.block (turn 12 ++
      ([.alu .add .esi (.imm 32), .alu .sub .ecx (.imm 1)] : List Instr))) .ne)
    (.block ((sumsOps 1 false).flatMap (LOp.instrs 12) ++ sumLanes ++ carryOps.flatMap (LOp.instrs 12) ++
      storeOut 12)))

/-- What the frame of 512 bytes runs: `h` into the frame and `r²` into `h`,
the lanes, and their result into `h`. -/
def pairsBody : Prog isa :=
  .seq (.block (saveH ++ ([.store (fs 0 cntOff) .ecx] : List Instr) ++ absorbAt .edi (rOff 0) 0 ++ reduce))
    (.seq (.frame (.mcdtEnter .eax) lanes .mcdtLeave)
      (.block (packH ++ wipeV)))

/-- Absorbs the `ecx ≥ 2` pairs of blocks at `esi`, which it advances past
them: `edi` holds `state`, after `setup`. -/
def pairs : Prog isa := .frame (.alloc 512) pairsBody (.free 512)

/-! ## `blocks(state, blocks, n)`

`esi` walks the blocks; the loop ends where it reaches `blocks + 16 n`,
recomputed from the arguments after each block. From 16 blocks on, the pairs
of blocks are absorbed first (`pairs`), and the loop absorbs the block that
may be left. -/

/-- `blocks + 16 n`, compared with `esi`. -/
def atEnd : List Instr :=
  [.mov .eax (.mem (at_ .esp 12)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .ecx (.mem (at_ .esp 8)),
    .alu .add .eax (.reg .ecx), .alu .cmp .eax (.reg .esi)]

def body : Prog isa :=
  .block (absorb 1 ++ ([.alu .add .esi (.imm 16)] : List Instr) ++ atEnd)

def blocks : Prog isa :=
  .seq (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
    .alu .cmp .ecx (.imm 16)] : List Instr)))
  (.seq (.ite .b (.block []) (.seq (.block [.shift .shr .ecx 1]) pairs))
  (.seq (.block atEnd)
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (reduce ++ restore)))))

/-! ## `update(state, count, data, len, scratch)`

With `esi` = the data not yet consumed (from `data = [esp + 16]`), whose
length is `data + len - esi` (`len = [esp + 20]`), recomputed when needed,
and `edx` = the number of bytes in the buffer (`count mod 16`, from `count`'s
low word `[esp + 8]`): a non-empty buffer is filled from the data (as far as
it goes) and, once full, absorbed; then the whole blocks of the data are
absorbed, and the rest is copied into the buffer. -/

/-- The length of the data not yet consumed, `data + len - esi`, into `eax`
(via `ecx`). -/
def left : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.mem (at_ .esp 20)), .alu .add .eax (.reg .ecx),
    .alu .sub .eax (.reg .esi)]

/-- Copies the `eax > 0` bytes at `esi` to `edx + 56`, advancing `esi` and
`edx`. -/
def copyIn : Prog isa :=
  .loop (.block [.movzx8 .ecx (at_ .esi 0), .store8 (at_ .edx 56) .cl, .alu .add .esi (.imm 1),
    .alu .add .edx (.imm 1), .alu .sub .eax (.imm 1)]) .ne

/-- The number of bytes to copy into the buffer, `min(16 - edx, len)`, into
`eax`, and `edx` made the address `state + edx`. -/
def count : Prog isa :=
  .seq (.block [.mov .eax (.imm 16), .alu .sub .eax (.reg .edx), .mov .ecx (.mem (at_ .esp 20)),
    .alu .cmp .ecx (.reg .eax)])
  (.seq (.ite .b (.block [.mov .eax (.reg .ecx)]) (.block []))
    (.block [.alu .add .edx (.reg .edi), .alu .test .eax (.reg .eax)]))

/-- Fills the buffer with `min(16 - edx, len)` bytes of the data, and absorbs
it if that fills it. -/
def fill : Prog isa :=
  .seq count
  (.seq (.ite .e (.block []) copyIn)
  (.seq (.block [.alu .sub .edx (.reg .edi), .alu .cmp .edx (.imm 16)])
    (.ite .e (.block (absorbAt .edi 56 1)) (.block []))))

/-- Absorbs the whole blocks of the data: from 16 on, a pair at a time while
there are two (`pairs`). -/
def whole : Prog isa :=
  .seq (.block (left ++ ([.alu .cmp .eax (.imm 256)] : List Instr)))
  (.seq (.ite .b (.block []) (.seq (.block [.mov .ecx (.reg .eax), .shift .shr .ecx 5]) pairs))
  (.seq (.block (left ++ ([.alu .cmp .eax (.imm 16)] : List Instr)))
    (.ite .b (.block [])
      (.loop (.block (absorb 1 ++ ([.alu .add .esi (.imm 16)] : List Instr) ++ left ++ ([.alu .cmp .eax (.imm 16)] : List Instr))) .ae))))

/-- Copies the rest of the data into the (empty) buffer. -/
def rest : Prog isa :=
  .seq (.block (left ++ ([.alu .test .eax (.reg .eax)] : List Instr)))
    (.ite .e (.block []) (.seq (.block [.mov .edx (.reg .edi)]) copyIn))

def update : Prog isa :=
  .seq (.block (setup ++ ([.mov .esi (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 8)),
    .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)] : List Instr)))
  (.seq (.ite .e (.block []) fill)
  (.seq whole
  (.seq rest
    (.block (reduce ++ restore)))))

/-! ## `finalize(state, count, out, scratch)`

`edx` = `count mod 16`, the number of bytes in the buffer. A non-empty
buffer is padded in place with zeros and then the `0x01` byte, and absorbed
with `pad = 0`. Then `h` is reduced and `s` added modulo `2¹²⁸`, into
`out = [esp + 16]`. -/

/-- Zeros the buffer from byte `edx < 16` on, at `ecx + 56 = state + edx + 56`. -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (at_ .ecx 56) .al, .alu .add .ecx (.imm 1), .alu .add .edx (.imm 1),
    .alu .cmp .edx (.imm 16)]) .ne

def lastBlock : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .mov .ecx (.reg .edx), .alu .add .ecx (.reg .edi)])
  (.seq zeroLoop
    (.block (([.mov .eax (.imm 1), .mov .ecx (.mem (at_ .esp 8)), .alu .and .ecx (.imm 15),
      .alu .add .ecx (.reg .edi), .store8 (at_ .ecx 56) .al] : List Instr) ++ absorbAt .edi 56 0)))

/-- The tag, `h + s` modulo `2¹²⁸`, into `out`. -/
def addS : List Instr :=
  .mov .esi (.mem (at_ .esp 16)) ::
  (List.range 4).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))),
    .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))), .store (at_ .esi (4 * k)) .eax]

def finalize : Prog isa :=
  .seq (.block (setup ++ ([.mov .edx (.mem (at_ .esp 8)), .alu .and .edx (.imm 15),
    .alu .test .edx (.reg .edx)] : List Instr)))
  (.seq (.ite .e (.block []) lastBlock)
    (.block (reduce ++ addS ++ restore)))

end VG.Impl.Poly1305.X86
