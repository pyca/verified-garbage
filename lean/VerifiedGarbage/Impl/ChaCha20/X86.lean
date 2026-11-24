module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# ChaCha20 block function: x86 (32-bit) implementation

`vg_chacha20_block(state, buf)`, cdecl: the arguments are at `[esp + 4]` and
`[esp + 8]`.

The state is in SSE2 registers, a row of four words each (`xmm0`–`xmm3`),
loaded from `state` (`eax`) a word at a time (`rowIn`):
* a column round is the quarter round on each doubleword of the four rows
  (`vqr`, with `xmm4` for the rotations), and a diagonal round the same
  after rows 1, 2 and 3 are rotated by one, two and three doublewords
  (`pshufd`), which are rotated back after it;
* finally each row of the input state (re-read from `state`, through
  `xmm4`) is added, and the row stored to `buf` (`ecx`).
* Only `eax`, `ecx`, `edx` and `xmm0`–`xmm5` are written, and of `buf` only its
  first 64 bytes. Every address is `esp`, `eax` or `ecx` plus a constant,
  and there are no branches, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## SSE2: the quarter round on each doubleword of four registers -/

/-- `op dst, src` on XMM registers. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `x` rotated left by `k` (`0 < k < 32`) in each doubleword, through `t`. -/
def vrot (x : XReg) (k : Nat) (t : XReg) : List Instr :=
  [xb .movdqa t x, .xop (.shift .pslld x (BitVec.ofNat 8 k)),
   .xop (.shift .psrld t (BitVec.ofNat 8 (32 - k))), xb .por x t]

/-- The quarter round (RFC 8439 §2.1) on each doubleword of `a, b, c, d`,
with `t` as scratch (for the block function, and the four-block code of
`vg_chacha20_xor`): a
rotation by 16 swaps the words of each doubleword (`pshuflw`, `pshufhw`), the
others are two shifts and an `or`. -/
def vqr (a b c d t : XReg) : List Instr :=
  [xb .paddd a b, xb .pxor d a, .xop (.pshuflw d d 0xb1), .xop (.pshufhw d d 0xb1),
   xb .paddd c d, xb .pxor b c] ++ vrot b 12 t ++
  [xb .paddd a b, xb .pxor d a] ++ vrot d 8 t ++
  [xb .paddd c d, xb .pxor b c] ++ vrot b 7 t

/-! ## The block function -/

/-- The register of row `r`. -/
def row : Nat → XReg
  | 0 => .xmm0
  | 1 => .xmm1
  | 2 => .xmm2
  | _ => .xmm3

/-- Row `r` of the state at `eax` into its register, a word at a time
(through `edx`, `xmm4` and `xmm5`): the callers have just stored the state's
words, and a 16-byte load would wait for those stores. -/
def rowIn (r : Nat) : List Instr :=
  [.mov .edx (.mem (at_ .eax (16 * r))), .xop (.movd (row r) .edx),
   .mov .edx (.mem (at_ .eax (16 * r + 4))), .xop (.movd .xmm4 .edx), xb .punpckldq (row r) .xmm4,
   .mov .edx (.mem (at_ .eax (16 * r + 8))), .xop (.movd .xmm4 .edx),
   .mov .edx (.mem (at_ .eax (16 * r + 12))), .xop (.movd .xmm5 .edx), xb .punpckldq .xmm4 .xmm5,
   xb .punpcklqdq (row r) .xmm4]

/-- `state` into `eax` and `buf` into `ecx`. -/
def loadArgs : List Instr := [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8))]

/-- The pointers, and the four rows of the state into `xmm0`–`xmm3`. -/
def rowsIn : List Instr := loadArgs ++ (List.range 4).flatMap rowIn

/-- Rows 1, 2 and 3 rotated by `i`, `j` and `k` doublewords (`pshufd`). -/
def shuf (i j k : BitVec 8) : List Instr :=
  [.xop (.pshufd .xmm1 .xmm1 i), .xop (.pshufd .xmm2 .xmm2 j), .xop (.pshufd .xmm3 .xmm3 k)]

/-- `inner_block` (RFC 8439 §2.3.1): a column round, and a diagonal round
between the rotations of the rows that bring each diagonal into a column and
back. -/
def doubleRound : Prog isa :=
  .block (vqr .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 ++ shuf 0x39 0x4e 0x93 ++
    vqr .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 ++ shuf 0x93 0x4e 0x39)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- Row `r` of the input state added to its register (through `xmm4`), and
the sum stored to `buf`. -/
def addRow (r : Nat) : List Instr :=
  [.movdquLoad .xmm4 (at_ .eax (16 * r)), xb .paddd (row r) .xmm4, .movdquStore (at_ .ecx (16 * r)) (row r)]

def finish : List Instr := (List.range 4).flatMap addRow

def block : Prog isa :=
  .seq (.block rowsIn) (.seq (rounds 10) (.block finish))

/-! ## SSSE3: the rotations by 16 and 8 bits of `vg_chacha20_xor_ssse3` -/

/-- Where `vqr3` finds its `pshufb` controls in `buf` (through `edi`). -/
def rot16Off : Nat := 288
def rot8Off : Nat := 304

/-- The `pshufb` controls that rotate each doubleword left by 16 and by 8
bits (byte `j` of a doubleword from byte `(j + 2) % 4`, resp. `(j + 3) % 4`),
as the words stored at `buf + rot16Off` and `buf + rot8Off`, and where. -/
def maskWords : List (BitVec 32 × Nat) :=
  [(0x01000302, 288), (0x05040706, 292), (0x09080b0a, 296), (0x0d0c0f0e, 300),
   (0x02010003, 304), (0x06050407, 308), (0x0a09080b, 312), (0x0e0d0c0f, 316)]

/-- The quarter round (RFC 8439 §2.1) on each doubleword of `a, b, c, d`
with SSSE3, with `t` as scratch: the rotations by 16 and 8 are `pshufb`
with the controls at `buf + rot16Off` and `buf + rot8Off`, loaded into
`t`; the others are two shifts and an `or`. -/
def vqr3 (a b c d t : XReg) : List Instr :=
  [xb .paddd a b, xb .pxor d a, .movdquLoad t (at_ .edi rot16Off), xb .pshufb d t,
   xb .paddd c d, xb .pxor b c] ++ vrot b 12 t ++
  [xb .paddd a b, xb .pxor d a, .movdquLoad t (at_ .edi rot8Off), xb .pshufb d t,
   xb .paddd c d, xb .pxor b c] ++ vrot b 7 t

/-- Stores the controls of `vqr3` in `buf` (`edi`), through `eax`. -/
def masks : List Instr := maskWords.flatMap fun p => [.mov .eax (.imm p.1), .store (at_ .edi p.2) .eax]

end VG.Impl.ChaCha20.X86
