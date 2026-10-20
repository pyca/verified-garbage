module

public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Spec.Rsa.MontMul

/-! # Montgomery multiplication at a width given at run time (32-bit x86)

`vg_rsa_mont_mul_at` (`Spec/Rsa/MontMul.lean`) takes the width and every
offset as arguments, so its code depends on none of them: it reaches the
numbers through pointers, the working space's address plus an offset, which
move by a word, and each loop ends when a pointer reaches an end it keeps in
memory. `edi` holds the base of the function's own range (at the offset
`s`), whose first words hold the pointers' ends, the rows' multiplier, the
inverse and the length `8 n` of a number in bytes (`ctl*`), then the
callee-saved registers, then the accumulator of `2 N + 1` words
(`N = 2 n` 32-bit words) and the subtraction's temporary of `N` words.

The arithmetic is `Dynamic.mul`'s: coarsely integrated operand scanning,
row `i` adding `a_i B` and then `q_i M` to the accumulator from word `i` on,
with `q_i` from `-M⁻¹`, and the conditional subtraction of `M` from the high
half, selected into the result by a mask. Every address is a pointer that
moves by a public step, and every branch is on a pointer reaching its end,
so the timing does not depend on the numbers.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Rt
open VG VG.X86 VG.Impl.Mont.X86

/-! ## The arguments and the function's own range -/

/-- The arguments on entry: `ws`, `ws_len`, `n`, then the offsets `m`, `inv`,
`s`, `o`, `a` and `b`. -/
def arg (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def argWs : MemOp := arg 0
def argN : MemOp := arg 2
def argM : MemOp := arg 3
def argInv : MemOp := arg 4
def argS : MemOp := arg 5
def argO : MemOp := arg 6
def argA : MemOp := arg 7
def argB : MemOp := arg 8

/-- The word of the function's own range holding a row's multiplier. -/
def multOff : Nat := 20

/-- Where the callee-saved registers go. -/
def saveSlots : List (Reg × Nat) := [(.ebx, 36), (.esi, 40), (.ebp, 44), (.edi, 48)]

/-- The accumulator's offset in the function's range: `2 N + 1` words, then
the subtraction's temporary of `N` words. -/
def accOff : Nat := 52

/-! ## The code

Everything public is in a register or computed from the arguments, which
are read-only: no public value goes through the working space. -/

/-- `r = ws + ` the offset argument `x`, through `t`: both are loaded, as
the taint analysis knows a register loaded from an argument public, not the
sum of a register and an argument in memory. -/
def ptr (r : Reg) (x : MemOp) (t : Reg) : List Instr := [.mov r (.mem argWs), .mov t (.mem x), .alu .add r (.reg t)]

/-- `r = 8 n` (the bytes of a number), times `2 ^ k` more. -/
def lenTimes (r : Reg) (k : Nat) : List Instr :=
  .mov r (.mem argN) :: List.replicate (3 + k) (.alu .add r (.reg r))

/-- `edi = ws + s`, the callee-saved registers saved. -/
def save : List Instr :=
  ptr .eax argS .edx ++ saveSlots.map (fun (r, d) => .store (at_ .eax d) r) ++ [.mov .edi (.reg .eax)]

/-- `ebp` at the accumulator. -/
def accPtr : List Instr := [.mov .ebp (.reg .edi), .alu .add .ebp (.imm (BitVec.ofNat 32 accOff))]

/-- The accumulator's `2 N + 1` words zeroed, `16 n + 4` bytes. -/
def zeroAcc : Prog isa :=
  .seq (.block (accPtr ++ lenTimes .esi 1 ++ [.alu .add .esi (.imm 4), .mov .eax (.imm 0)]))
    (.loop (.block [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]) .ne)

/-- One step of a row: `[ebp] += [multOff] · [ecx]` with the carry `ebx`,
both pointers up a word, `esi` down 4; ZF when it reaches zero. -/
def mulStep : List Instr :=
  [.mov .eax (.mem (sc multOff)), .mov .edx (.mem (at_ .ecx 0)), .mul .edx,
   .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0),
   .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
   .alu .add .ecx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]

/-- `mulStep` with the multiplier at `[edi + mo]`. -/
def mulStepAt (mo : Nat) : List Instr :=
  [.mov .eax (.mem (sc mo)), .mov .edx (.mem (at_ .ecx 0)), .mul .edx,
   .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0),
   .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
   .alu .add .ecx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]

/-- The carry `ebx` into the two words at `ebp`. -/
def carryWords : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .add .eax (.reg .ebx), .store (at_ .ebp 0) .eax,
   .mov .eax (.mem (at_ .ebp 4)), .alu .adc .eax (.imm 0), .store (at_ .ebp 4) .eax]

/-- The carry, and `ebp` back to the row's start. -/
def carryUp : List Instr := carryWords ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]

/-- The window at `ebp` `+= [multOff] ·` the number at the offset argument `x`. -/
def mulRow (x : MemOp) : Prog isa :=
  .seq (.block ([.mov .ebx (.imm 0)] ++ ptr .ecx x .edx ++ lenTimes .esi 0)) <|
  .seq (.loop (.block mulStep) .ne) (.block carryUp)

/-- `a_i` into `multOff`: at `ws + a + 4 i`, for `ebp` at word `i` of the accumulator. -/
def loadA : List Instr :=
  [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .edi), .alu .sub .eax (.imm (BitVec.ofNat 32 accOff)),
   .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA), .alu .add .eax (.reg .edx),
   .mov .eax (.mem (at_ .eax 0)), .store (sc multOff) .eax]

/-- `q = [ebp] · -M⁻¹ mod 2³²` into `multOff`. -/
def redDigit : List Instr :=
  ptr .edx argInv .eax ++
    [.mov .edx (.mem (at_ .edx 0)), .mov .eax (.mem (at_ .ebp 0)), .mul .edx, .store (sc multOff) .eax]

/-- `ebp` up a word; ZF at the end of the rows, `8 n` bytes past the accumulator. -/
def rowEnd : List Instr :=
  [.alu .add .ebp (.imm 4)] ++ lenTimes .eax 0 ++
    [.alu .add .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 accOff)), .alu .cmp .ebp (.reg .eax)]

/-- A row: `a_i B`, then `q M`, into the accumulator from word `i`. -/
def row : Prog isa :=
  .seq (.block loadA) <|
  .seq (mulRow argB) <|
  .seq (.block redDigit) <|
  .seq (mulRow argM) (.block rowEnd)

def rows : Prog isa := .seq (.block accPtr) (.loop row .ne)

/-- The carry flag from the mask `ecx`. -/
def restore : List Instr := [.mov .edx (.imm 0), .alu .cmp .edx (.reg .ecx)]

/-- The temporary (past the accumulator's top word) `=` the high half (at
`ebp`) `- M`, the borrow as a mask in `ecx`, with `edi` counting down; `ebp`
ends at the top word, and `edi` is set back. -/
def subM : Prog isa :=
  .seq (.block (lenTimes .ebx 0 ++ [.alu .add .ebx (.reg .ebp), .alu .add .ebx (.imm 4)] ++
      ptr .esi argM .eax ++ lenTimes .edi 0 ++ [.mov .ecx (.imm 0)])) <|
  .seq (.loop (.block ([.mov .eax (.mem (at_ .ebp 0))] ++ restore ++
      [.alu .sbb .eax (.mem (at_ .esi 0)), .store (at_ .ebx 0) .eax, .alu .sbb .ecx (.reg .ecx),
       .alu .add .ebp (.imm 4), .alu .add .esi (.imm 4), .alu .add .ebx (.imm 4),
       .alu .sub .edi (.imm 4)])) .ne)
    (.block (ptr .edi argS .eax))

/-- The mask `ecx`: all ones if the high half with its top word is at least `M`. -/
def mask : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0))] ++ restore ++
    [.alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1)), .mov .ecx (.reg .eax)]

/-- The result at `o`: the temporary where the mask is all ones, else the high half. -/
def select : Prog isa :=
  .seq (.block (lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax), .mov .ebx (.reg .ebp),
      .alu .add .ebx (.reg .eax), .alu .add .ebx (.imm 4)] ++
      ptr .esi argO .edx ++ [.mov .edi (.reg .eax)]))
    (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .mov .edx (.mem (at_ .ebx 0)),
      .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
      .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4),
      .alu .sub .edi (.imm 4)]) .ne)

/-- The callee-saved registers back, `edi` last. -/
def restoreRegs : List Instr :=
  ptr .edi argS .eax ++ saveSlots.map fun (r, d) => .mov r (.mem (sc d))

def body : Prog isa :=
  .seq (.block save) <|
  .seq zeroAcc <|
  .seq rows <|
  .seq subM <|
  .seq (.block mask) <|
  .seq select (.block restoreRegs)

end VG.Impl.Mont.X86.Rt
