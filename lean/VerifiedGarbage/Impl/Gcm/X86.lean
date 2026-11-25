module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# GHASH: x86 (32-bit) implementation, in SSE2

`vg_ghash(h, y, data, n, scratch)`, cdecl: the arguments are at `[esp + 4]`
… `[esp + 20]`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, the product of
SP 800-38D as a sum of multiples `H·xⁱ` of `H`, each under the mask of a bit
of `Y ⊕ X`:

* A block is in a register as its 128-bit value, the first byte the most
  significant (`swap` reverses the bytes), so that its most significant bit
  is the coefficient of `x⁰`.
* The table, built once per call (`table`): `Tᵢ = H·xⁱ`, reduced, for
  `i < 8`, in the slot `i` of the scratch buffer.
* The 16 bytes of `Y ⊕ X` are taken in four groups of four, a group the even
  or the odd bytes of one of its halves. The words of the half are each
  duplicated into a doubleword of `xmm4`; a step (`step`) takes the top bit
  of each word as its mask (`psraw`), shifts the words left by one bit
  (`paddw`), and adds `Tᵢ` under each of the four masks, broadcast, to each
  of four accumulators (`xmm0` to `xmm3`). Eight steps are a group, and the
  eight after them the group of the other bytes.
* `horner` adds a group's accumulators, each times a power of `x¹⁶`, without
  reducing: the sum is `Z + x¹²⁸·O`, with `Z` in `xmm3` and `O` in `xmm5`
  (whose lowest bits are 0, as the sum's degree is bounded). `addOdd` adds
  the group of the odd bytes, times `x⁸`, to that of the even bytes, and
  `addLow` the low half's sum, times `x⁶⁴`, to the high half's.
* `reduce`: `x¹²⁸ = 1 + x + x² + x⁷`, so `Y := Z ⊕ O ⊕ O·x ⊕ O·x² ⊕ O·x⁷`,
  where the multiples of `O` are shifts, as its lowest eight bits are 0.

Every address is `esp` or a pointer plus a constant, and every branch
depends only on `n`, so only the pointers and `n` can affect timing. No
register but `eax`, `ecx` and `edx` is used, so none is saved.

The slots of the scratch buffer (`slot k`, the 16 bytes at `16 k`): 0 to 7
the table; 8 and 9 the `Z` and `O` of the even bytes' group; 10 `Y ⊕ X`; 11
and 12 the `Z` and `O` of the low half; 13 the constant `swap` uses.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Argument `i` on entry (cdecl). -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- The slot `k` of the scratch buffer, with `scratch` in `edx`. -/
def slot (k : Nat) : MemOp := at_ .edx (16 * k)

/-- The low byte of each word. -/
def lowBytes : BitVec 32 := 0x00ff00ff

/-- The bytes of `x` reversed, with `lowBytes` in each doubleword of `k`: the
doublewords, then the words of each, then the bytes of each. -/
def swap (x t k : XReg) : List Instr :=
  [.xop (.pshufd x x 0x1b), .xop (.pshuflw x x 0xb1), .xop (.pshufhw x x 0xb1),
   .xop (.bin .movdqa t x), .xop (.shift .psrld t 8), .xop (.bin .pand t k),
   .xop (.bin .pand x k), .xop (.shift .pslld x 8), .xop (.bin .por x t)]

/-- `V := V·x`, for `V` in `xmm0`, with `rMask` in `xmm2`: each half shifted
right by one bit, plus the part of `rMask` in it if the other half's lowest
bit is 1 (a mask of the top word of the half that bit was in, moved across).
That is the bit carried into the low half, and in the high half the reduction
of the bit shifted out of `V`. -/
def mulX : List Instr :=
  [.xop (.bin .movdqa .xmm1 .xmm0), .xop (.shift .psllq .xmm1 63), .xop (.shift .psraw .xmm1 15),
   .xop (.pshufd .xmm1 .xmm1 0x4e), .xop (.bin .pand .xmm1 .xmm2), .xop (.shift .psrlq .xmm0 1),
   .xop (.bin .pxor .xmm0 .xmm1)]

/-- `scratch` into `edx`, and `swap`'s constant into `xmm7` and the slot 13. -/
def start : List Instr :=
  ([.mov .edx (.mem (argOp 4)), .mov .eax (.imm lowBytes), .xop (.movd .xmm7 .eax),
    .xop (.pshufd .xmm7 .xmm7 0)] : List Instr) ++ ([.movdquStore (slot 13) .xmm7] : List Instr)

/-- `mulX`'s constant into `xmm2`: the top word of `R` in the top word, and
the top bit of the low half. -/
def rMask : List Instr :=
  [.mov .eax (.imm 0xe1000000), .xop (.movd .xmm2 .eax), .mov .eax (.imm 0x80000000),
   .xop (.movd .xmm3 .eax), .xop (.bin .punpckldq .xmm3 .xmm2), .xop (.bin .pxor .xmm2 .xmm2),
   .xop (.bin .punpckldq .xmm2 .xmm3)]

/-- `H` into `xmm0`. -/
def loadH : List Instr :=
  ([.mov .eax (.mem (argOp 0)), .movdquLoad .xmm0 (at_ .eax 0)] : List Instr) ++ swap .xmm0 .xmm1 .xmm7

/-- `Tᵢ` into the slot `i`, and `xmm0` to the next. -/
def entry (i : Nat) : List Instr := .movdquStore (slot i) .xmm0 :: mulX

/-- The table, from `H` in `xmm0` (and the first one past it left there). -/
def table : List Instr := (List.range 8).flatMap entry

/-- `Y` into `xmm3`, and the data pointer into `eax`. -/
def loadY : List Instr :=
  ([.mov .eax (.mem (argOp 1)), .movdquLoad .xmm3 (at_ .eax 0)] : List Instr) ++
  (swap .xmm3 .xmm1 .xmm7 ++ ([.mov .eax (.mem (argOp 2))] : List Instr))

/-- `Y ⊕ X` into `xmm4` and the slot 10. -/
def loadX : List Instr :=
  ([.movdquLoad .xmm4 (at_ .eax 0)] : List Instr) ++ (swap .xmm4 .xmm5 .xmm7 ++
  ([.xop (.bin .pxor .xmm4 .xmm3), .movdquStore (slot 10) .xmm4] : List Instr))

/-- `Tᵢ` into `xmm6`, the masks of the top bits of the words of `xmm4` into
`xmm5`, and the words shifted. -/
def masks (i : Nat) : List Instr :=
  [.movdquLoad .xmm6 (slot i), .xop (.bin .movdqa .xmm5 .xmm4), .xop (.shift .psraw .xmm5 15),
   .xop (.bin .paddw .xmm4 .xmm4)]

/-- The register of the accumulator `q`. -/
def acc : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

/-- `pshufd`'s order that broadcasts the doubleword whose mask the accumulator
`q` takes: the accumulator 0 the top one, which holds the lowest powers. -/
def bcast : Nat → BitVec 8
  | 0 => 0xff | 1 => 0xaa | 2 => 0x55 | _ => 0x00

/-- `A_q := Tᵢ` under its mask. -/
def set (q : Nat) : List Instr :=
  [.xop (.pshufd (acc q) .xmm5 (bcast q)), .xop (.bin .pand (acc q) .xmm6)]

/-- `A_q ⊕= Tᵢ` under its mask. -/
def add (q : Nat) : List Instr :=
  [.xop (.pshufd .xmm7 .xmm5 (bcast q)), .xop (.bin .pand .xmm7 .xmm6), .xop (.bin .pxor (acc q) .xmm7)]

/-- The first step of a group, which sets the accumulators. -/
def step0 : List Instr := masks 0 ++ (set 0 ++ (set 1 ++ (set 2 ++ set 3)))

/-- Step `i` of a group. -/
def step (i : Nat) : List Instr := masks i ++ (add 0 ++ (add 1 ++ (add 2 ++ add 3)))

/-- The accumulators of eight bits of each word. -/
def group : List Instr := step0 ++ (List.range 7).flatMap fun i => step (i + 1)

/-- `(Z, O) := (Z, O)·x¹⁶ ⊕ A_q`. -/
def shift16 (q : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm6 .xmm3), .xop (.shift .pslldq .xmm6 14), .xop (.shift .psrldq .xmm5 2),
   .xop (.bin .pxor .xmm5 .xmm6), .xop (.shift .psrldq .xmm3 2), .xop (.bin .pxor .xmm3 (acc q))]

/-- The sum of the accumulators `A_q`, times `x^(16 q)`. -/
def horner : List Instr :=
  ([.xop (.bin .movdqa .xmm5 .xmm3), .xop (.shift .pslldq .xmm5 14), .xop (.shift .psrldq .xmm3 2),
    .xop (.bin .pxor .xmm3 .xmm2)] : List Instr) ++ (shift16 1 ++ shift16 0)

/-- `Z` and `O` into the slots `a` and `a + 1`. -/
def save (a : Nat) : List Instr := [.movdquStore (slot a) .xmm3, .movdquStore (slot (a + 1)) .xmm5]

/-- `(Z, O) := (Z, O)·x⁸`. -/
def shift8 : List Instr :=
  [.xop (.bin .movdqa .xmm6 .xmm3), .xop (.shift .pslldq .xmm6 15), .xop (.shift .psrldq .xmm3 1),
   .xop (.shift .psrldq .xmm5 1), .xop (.bin .pxor .xmm5 .xmm6)]

/-- The slot `k` added to `r`. -/
def addSlot (r : XReg) (k : Nat) : List Instr := [.movdquLoad .xmm6 (slot k), .xop (.bin .pxor r .xmm6)]

/-- The odd bytes' group in `(Z, O)`, times `x⁸`, plus the even bytes'. -/
def addOdd : List Instr := shift8 ++ (addSlot .xmm3 8 ++ addSlot .xmm5 9)

/-- The sum of a half, whose duplicated words are in `xmm4`. -/
def half : List Instr := group ++ (horner ++ (save 8 ++ (group ++ (horner ++ addOdd))))

/-- `(Z, O)`, plus the low half's times `x⁶⁴`. -/
def addLow : List Instr :=
  [.movdquLoad .xmm6 (slot 11), .movdquLoad .xmm7 (slot 12), .xop (.bin .movdqa .xmm0 .xmm6),
   .xop (.shift .pslldq .xmm0 8), .xop (.shift .psrldq .xmm6 8), .xop (.shift .psrldq .xmm7 8),
   .xop (.bin .pxor .xmm3 .xmm6), .xop (.bin .pxor .xmm5 .xmm0), .xop (.bin .pxor .xmm5 .xmm7)]

/-- `Y := Z ⊕ O ⊕ O·x ⊕ O·x² ⊕ O·x⁷` into `xmm3`: the bits that the shifts
carry from the high half of `O` into the low one (`xmm6`), then the shifts of
each half. -/
def reduce : List Instr :=
  [.xop (.bin .movdqa .xmm6 .xmm5), .xop (.shift .psllq .xmm6 57), .xop (.bin .movdqa .xmm7 .xmm6),
   .xop (.shift .psllq .xmm7 5), .xop (.bin .pxor .xmm6 .xmm7), .xop (.shift .psllq .xmm7 1),
   .xop (.bin .pxor .xmm6 .xmm7), .xop (.shift .psrldq .xmm6 8), .xop (.bin .pxor .xmm3 .xmm6),
   .xop (.bin .pxor .xmm3 .xmm5), .xop (.shift .psrlq .xmm5 1), .xop (.bin .pxor .xmm3 .xmm5),
   .xop (.shift .psrlq .xmm5 1), .xop (.bin .pxor .xmm3 .xmm5), .xop (.shift .psrlq .xmm5 5),
   .xop (.bin .pxor .xmm3 .xmm5)]

/-- `swap`'s constant into `xmm7`, the next block, and one fewer (ZF is set
after the last block). -/
def next : List Instr :=
  [.movdquLoad .xmm7 (slot 13), .alu .add .eax (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The low half of `Y ⊕ X`. -/
def low : List Instr := ([.xop (.bin .punpcklwd .xmm4 .xmm4)] : List Instr) ++ (half ++ save 11)

/-- The high half of `Y ⊕ X`, and the low half's sum. -/
def high : List Instr :=
  ([.movdquLoad .xmm4 (slot 10), .xop (.bin .punpckhwd .xmm4 .xmm4)] : List Instr) ++ (half ++ addLow)

/-- One block: `Y` in `xmm3`, and the block at `eax`. -/
def body : List Instr := loadX ++ (low ++ (high ++ (reduce ++ next)))

/-- `Y` stored. -/
def finish : List Instr :=
  swap .xmm3 .xmm1 .xmm7 ++ ([.mov .eax (.mem (argOp 1)), .movdquStore (at_ .eax 0) .xmm3] : List Instr)

/-- The number of blocks (ZF is set if it is zero). -/
def count : List Instr := [.mov .ecx (.mem (argOp 3)), .alu .test .ecx (.reg .ecx)]

/-- The constants, the table, `Y` in `xmm3` and the data pointer in `eax`. -/
def setup : List Instr := start ++ (rMask ++ (loadH ++ (table ++ loadY)))

/-- If there are no blocks, `Y` is left as it is. -/
def ghash : Prog isa :=
  .seq (.block count)
    (.ite .e (.block [])
      (.seq (.block setup) (.seq (.loop (.block body) .ne) (.block finish))))

end VG.Impl.Gcm.X86
