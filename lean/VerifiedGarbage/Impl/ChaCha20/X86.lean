import VerifiedGarbage.TCB.X86.Isa

/-!
# ChaCha20 block function: x86 (32-bit) implementation, with SSE2

`vg_chacha20_block(state, buf)`, cdecl: the arguments are at `[esp + 4]` and
`[esp + 8]`.

The four rows of the state are in `xmm0, …, xmm3` (doubleword `i` of `xmmr`
holding word `4 r + i`), as in OpenSSL's `chacha-x86.pl`: a quarter round on
each doubleword of the four registers (`vqr`) is the column round; rotating
the doublewords of rows 1, 2 and 3 by one, two and three places (`pshufd`)
lines the diagonals up in the doublewords, and a second `vqr` is the
diagonal round, after which the rows are rotated back. Finally the input
state, reloaded a row at a time into `xmm4`, is added, and the rows are
stored to the first 64 bytes of `buf`.

`eax` holds `state` and `ecx` `buf`; no callee-saved register is written and
no stack is used. There are no branches and every address is `esp`, `eax`
or `ecx` plus a constant, so only the pointers can affect timing.
-/

namespace VG.Impl.ChaCha20.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `op dst, src` on XMM registers. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `x` rotated left by `k` (`0 < k < 32`) in each doubleword, through `xmm4`. -/
def vrot (x : XReg) (k : Nat) : List Instr :=
  [xb .movdqa .xmm4 x, .xop (.shift .pslld x (BitVec.ofNat 8 k)),
   .xop (.shift .psrld .xmm4 (BitVec.ofNat 8 (32 - k))), xb .por x .xmm4]

/-- The quarter round (RFC 8439 §2.1) on each doubleword of `xmm0, xmm1,
xmm2, xmm3`, with `xmm4` as scratch: a rotation by 16 swaps the words of
each doubleword (`pshuflw`, `pshufhw`), the others are two shifts and an
`or`. -/
def vqr : List Instr :=
  [xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0, .xop (.pshuflw .xmm3 .xmm3 0xb1),
   .xop (.pshufhw .xmm3 .xmm3 0xb1),
   xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2] ++ vrot .xmm1 12 ++
  [xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0] ++ vrot .xmm3 8 ++
  [xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2] ++ vrot .xmm1 7

/-- Rows 1, 2 and 3 rotated by one, two and three doublewords, so that
doubleword `i` of the four rows holds diagonal `i`. -/
def diag : List Instr :=
  [.xop (.pshufd .xmm1 .xmm1 0x39), .xop (.pshufd .xmm2 .xmm2 0x4e), .xop (.pshufd .xmm3 .xmm3 0x93)]

/-- The rotations of `diag` undone. -/
def undiag : List Instr :=
  [.xop (.pshufd .xmm1 .xmm1 0x93), .xop (.pshufd .xmm2 .xmm2 0x4e), .xop (.pshufd .xmm3 .xmm3 0x39)]

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round. -/
def doubleRound : Prog isa := .block (vqr ++ (diag ++ (vqr ++ undiag)))

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- The pointers into `eax` and `ecx`, and the state into `xmm0, …, xmm3`. -/
def load : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8)),
   .movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .eax 16),
   .movdquLoad .xmm2 (at_ .eax 32), .movdquLoad .xmm3 (at_ .eax 48)]

/-- Row `r` (in `x`) plus row `r` of the input state, stored to `buf`. -/
def addRow (x : XReg) (r : Nat) : List Instr :=
  [.movdquLoad .xmm4 (at_ .eax (16 * r)), xb .paddd x .xmm4, .movdquStore (at_ .ecx (16 * r)) x]

def finish : List Instr :=
  addRow .xmm0 0 ++ addRow .xmm1 1 ++ addRow .xmm2 2 ++ addRow .xmm3 3

def block : Prog isa := .seq (.block load) (.seq (rounds 10) (.block finish))

end VG.Impl.ChaCha20.X86
