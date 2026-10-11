module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.X86.Isa

/-!
# BLAKE2s compression function: x86 (32-bit) implementation, with SSE2

`vg_blake2s_compress(state, blocks, n, t, last, scratch)`, cdecl: the
arguments are at `[esp + 4]` (`state`), `[esp + 8]` (`blocks`), `[esp + 12]`
(`n`), `[esp + 16]` and `[esp + 20]` (the low and high words of `t`),
`[esp + 24]` (`last`) and `[esp + 28]` (`scratch`).

The four rows of the work vector `v` are in `xmm0, …, xmm3` (doubleword `i`
of `xmm r` holding word `4 r + i`): `G` on each doubleword of the four
registers (`vg`) is the four `G`s on the columns; rotating the doublewords of
rows 0, 2 and 3 by three, one and two places (`pshufd`) lines the diagonals
up in the doublewords, and a second `vg` is the four `G`s on the diagonals,
after which the rows are rotated back. The message words of each half round
are gathered into `xmm5` and `xmm6` (doubleword `i` holding those of the
`G` whose words are in doubleword `i`): SSE2 has no byte or doubleword permutation across registers
that would do it in fewer instructions, so each word is loaded into `ecx` or
`edx`, moved to an XMM register (`movd`) and interleaved (`punpckldq`,
`punpcklqdq`), through `xmm4` and `xmm7`. The rotations by 16 swap the words
of each doubleword (`pshuflw`, `pshufhw`), the others are two shifts and an
`or`. The rounds are fully unrolled.

`scratch` is laid out as:

* `[32, 64)`: words 8 to 15 of the work vector before the rounds (the IV,
  with the offset counter and the final block flag), loaded into `xmm2` and
  `xmm3`;
* `[64, 72)`: the offset counter of the current block (low word, then high);
* `[72, 76)`: the final block flag, as all-zero or all-one bits;
* `[76, 80)`: the number of blocks left;
* `[80, 92)`: the saved `ebx`, `esi` and `edi` (`ebp` is not used).

`esi` points to `scratch`, `edi` to the current block and `eax` to the hash
value during each block. Every address is `esp`, `eax`, `esi` or `edi` plus a
constant, and the only branches are on `last` and on the count of blocks, so
only the pointers, `n`, `t` and `last` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Blake2.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

namespace CompressS

/-! ## The layout of `scratch` -/

/-- Word `k` of the work vector (for `8 ≤ k < 16`, before the rounds). -/
def vOff (k : Nat) : Nat := 4 * k
def tloOff : Nat := 64
def thiOff : Nat := 68
def fOff : Nat := 72
def nOff : Nat := 76

/-! ## The rounds -/

/-- `op dst, src` on XMM registers. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `x` rotated right by `k` (`0 < k < 32`) in each doubleword, through `xmm4`. -/
def vror (x : XReg) (k : Nat) : List Instr :=
  [xb .movdqa .xmm4 x, .xop (.shift .psrld x (BitVec.ofNat 8 k)),
   .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 (32 - k))), xb .por x .xmm4]

/-- `G` (RFC 7693 §3.1) on each doubleword of `xmm0, xmm1, xmm2, xmm3` (`a`,
`b`, `c`, `d`), with the message words in `xmm5` (`x`) and `xmm6` (`y`) and
`xmm4` as scratch. BLAKE2s's rotations are by 16, 12, 8 and 7. Each
`a := a + b + x` adds `x` first: `a` is ready before `b`, which the step
before computes last, so the chain of dependent instructions is one shorter. -/
def vg : List Instr :=
  [xb .paddd .xmm0 .xmm5, xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0,
   .xop (.pshuflw .xmm3 .xmm3 0xb1), .xop (.pshufhw .xmm3 .xmm3 0xb1),
   xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2] ++ vror .xmm1 12 ++
  [xb .paddd .xmm0 .xmm6, xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0] ++ vror .xmm3 8 ++
  [xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2] ++ vror .xmm1 7

/-- Rows 0, 2 and 3 rotated by three, one and two doublewords, so that
doubleword `i` of the four rows holds diagonal `i - 1` (modulo 4). Row 1
stays: `b`, which `G` computes last, is the first operand the next `G`
needs. -/
def diag : List Instr :=
  [.xop (.pshufd .xmm0 .xmm0 0x93), .xop (.pshufd .xmm2 .xmm2 0x39), .xop (.pshufd .xmm3 .xmm3 0x4e)]

/-- The rotations of `diag` undone. -/
def undiag : List Instr :=
  [.xop (.pshufd .xmm0 .xmm0 0x39), .xop (.pshufd .xmm2 .xmm2 0x93), .xop (.pshufd .xmm3 .xmm3 0x4e)]

/-- The `G` whose words are in doubleword `i` in half `k` of a round: `G`
`i` on the columns (`k = 0`), `G` `i - 1` (modulo 4) on the diagonals. -/
def lane (k i : Nat) : Nat := if k = 0 then i else (i + 3) % 4

/-- Words `f 0, f 1, f 2, f 3` of the block (at `edi`) into doublewords 0 to 3
of `x`, through `ecx`, `edx`, `xmm4` and `xmm7`. -/
def gather (x : XReg) (f : Nat → Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .edi (4 * f 0))), .mov .edx (.mem (at_ .edi (4 * f 1))),
   .xop (.movd x .ecx), .xop (.movd .xmm7 .edx), xb .punpckldq x .xmm7,
   .mov .ecx (.mem (at_ .edi (4 * f 2))), .mov .edx (.mem (at_ .edi (4 * f 3))),
   .xop (.movd .xmm4 .ecx), .xop (.movd .xmm7 .edx), xb .punpckldq .xmm4 .xmm7,
   xb .punpcklqdq x .xmm4]

/-- The message words of the four `G`s of half `k` of round `r` (the columns
for `k = 0`, the diagonals for `k = 1`): the first of each into `xmm5`, the
second into `xmm6`, those of `G` `lane k i` in doubleword `i`. -/
def msgs (r k : Nat) : List Instr :=
  gather .xmm5 (fun i => (Spec.Blake2.sigmaAt r (8 * k + 2 * lane k i)).val) ++
  gather .xmm6 (fun i => (Spec.Blake2.sigmaAt r (8 * k + 2 * lane k i + 1)).val)

/-- Round `r` (RFC 7693 §3.2): the columns, then the diagonals. -/
def round (r : Nat) : Prog isa :=
  .seq (.block (msgs r 0)) <| .seq (.block vg) <| .seq (.block diag) <|
  .seq (.block (msgs r 1)) <| .seq (.block vg) (.block undiag)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

/-! ## One block -/

/-- Initialize the work vector (RFC 7693 §3.2): words 8 to 15 (the IV, with
the offset counter and the final block flag XORed into words 12 to 14) are
stored to `scratch` through `ecx`, and the rows loaded: the hash value from
`eax` (loaded from its argument slot), the rest from `scratch`. -/
def load : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)),
   .mov .ecx (.imm Spec.Blake2.s.IV[0]), .store (at_ .esi (vOff 8)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[1]), .store (at_ .esi (vOff 9)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[2]), .store (at_ .esi (vOff 10)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[3]), .store (at_ .esi (vOff 11)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[4]), .alu .xor .ecx (.mem (at_ .esi tloOff)),
   .store (at_ .esi (vOff 12)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[5]), .alu .xor .ecx (.mem (at_ .esi thiOff)),
   .store (at_ .esi (vOff 13)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[6]), .alu .xor .ecx (.mem (at_ .esi fOff)),
   .store (at_ .esi (vOff 14)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[7]), .store (at_ .esi (vOff 15)) .ecx,
   .movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .eax 16),
   .movdquLoad .xmm2 (at_ .esi (vOff 8)), .movdquLoad .xmm3 (at_ .esi (vOff 12))]

/-- XOR the two halves of the work vector into the hash value (at `eax`):
`h[i] := v[i] ^ v[i + 8] ^ h[i]`. -/
def finish : List Instr :=
  [xb .pxor .xmm0 .xmm2, xb .pxor .xmm1 .xmm3,
   .movdquLoad .xmm4 (at_ .eax 0), xb .pxor .xmm0 .xmm4, .movdquStore (at_ .eax 0) .xmm0,
   .movdquLoad .xmm4 (at_ .eax 16), xb .pxor .xmm1 .xmm4, .movdquStore (at_ .eax 16) .xmm1]

/-- Advance to the next block and its offset counter (a 64-bit integer: the
carry goes to the high word), and decrement the count of blocks (setting ZF
when it hits 0). -/
def advance : List Instr :=
  [.alu .add .edi (.imm 64),
   .mov .eax (.mem (at_ .esi tloOff)), .alu .add .eax (.imm 64), .store (at_ .esi tloOff) .eax,
   .mov .eax (.mem (at_ .esi thiOff)), .alu .adc .eax (.imm 0), .store (at_ .esi thiOff) .eax,
   .mov .eax (.mem (at_ .esi nOff)), .alu .sub .eax (.imm 1), .store (at_ .esi nOff) .eax]

def body : Prog isa := .seq (.block load) (.seq (rounds 10) (.block (finish ++ advance)))

/-! ## The whole function -/

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 80), (.esi, 84), (.edi, 88)]

/-- Save the callee-saved registers (with `scratch` in `eax`), keep the
offset counter in `scratch`, and test `last`. -/
def prologue : List Instr :=
  ([.mov .eax (.mem (at_ .esp 28))] : List Instr) ++ saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  ([.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)),
   .mov .eax (.mem (at_ .esp 16)), .store (at_ .esi tloOff) .eax,
   .mov .eax (.mem (at_ .esp 20)), .store (at_ .esi thiOff) .eax,
   .mov .ecx (.imm 0), .mov .eax (.mem (at_ .esp 24)), .alu .test .eax (.reg .eax)] : List Instr)

/-- The final block flag (all one bits if `last ≠ 0`), and the count of
blocks, setting ZF if it is 0. -/
def flag : Prog isa :=
  .seq (.ite .e (.block []) (.block [.mov .ecx (.imm 0xffffffff)]))
    (.block [.store (at_ .esi fOff) .ecx, .mov .eax (.mem (at_ .esp 12)), .store (at_ .esi nOff) .eax,
      .alu .test .eax (.reg .eax)])

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (.mem (at_ .esi 80)), .mov .edi (.mem (at_ .esi 88)), .mov .esi (.mem (at_ .esi 84))]

def compress : Prog isa :=
  .seq (.block prologue) (.seq flag (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue)))

end CompressS

end VG.Impl.Blake2.X86
