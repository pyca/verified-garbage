import VerifiedGarbage.TCB.X86.Isa

/-!
# The Salsa20/8 Core: x86 (32-bit) implementation, with SSE2

`vg_salsa20_8(b = [esp + 4], scratch = [esp + 8])`, every argument on the
stack (cdecl): replaces the 64 bytes at `b` by their Salsa20/8 Core
(RFC 7914 §3).

The sixteen words live in `xmm0, …, xmm3` in the diagonal layout of
OpenSSL's and libsodium's SSE2 Salsa20: doubleword `q` of `xmm k` holds word
`5 q + 4 k` (modulo 16), so that doubleword `q` of the four registers holds
column `q` of the matrix, starting from its diagonal word. Each line
`x[i] ^= R(x[j] + x[k], n)` of the column round is then one `vstep` on the
four columns at once (the rotation as two shifts, both XORed in); with
`xmm1, xmm2, xmm3` rotated by three, two and one doublewords (`pshufd`),
doubleword `q` holds row `q`, and the same code with `xmm1` and `xmm3`
swapped is the row round. The four double rounds are fully unrolled.

The rows of the input are loaded (`movdqu`) and put into that layout by
rotating rows 1 to 3 by one, two and three doublewords, transposing the
matrix (`punpck{l,h}{dq,qdq}`) and rotating three of the results; the result
is put back the inverse way, the input rows (still in `b`) added, and stored.
`scratch` is not used; only `eax` (`b`) and the XMM registers are written.

Every address is `esp` or `eax` plus a constant, and there are no branches,
so only the pointers can affect timing.
-/

namespace VG.Impl.Scrypt.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `op dst, src` on XMM registers. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `pshufd dst, src, order`. -/
def shuf (d r : XReg) (o : BitVec 8) : Instr := .xop (.pshufd d r o)

/-- `x ^= R(y + z, n)` on each doubleword, through `xmm4` and `xmm5`. -/
def vstep (x y z : XReg) (n : Nat) : List Instr :=
  [xb .movdqa .xmm4 y, xb .paddd .xmm4 z, xb .movdqa .xmm5 .xmm4,
   .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 n)), .xop (.shift .psrld .xmm5 (BitVec.ofNat 8 (32 - n))),
   xb .pxor x .xmm4, xb .pxor x .xmm5]

/-- The four quarter rounds on the doublewords of `xmm0` (the first word of
each) and `b`, `c`, `d`, in the order of RFC 7914 §3: the column round with
`b, c, d = xmm1, xmm2, xmm3`, the row round with `xmm3, xmm2, xmm1`. -/
def vhalf (b c d : XReg) : List Instr :=
  vstep b .xmm0 d 7 ++ vstep c b .xmm0 9 ++ vstep d c b 13 ++ vstep .xmm0 d c 18

/-- From columns to rows in the doublewords. -/
def toRows : List Instr := [shuf .xmm1 .xmm1 0x93, shuf .xmm2 .xmm2 0x4e, shuf .xmm3 .xmm3 0x39]

/-- From rows to columns in the doublewords. -/
def toCols : List Instr := [shuf .xmm1 .xmm1 0x39, shuf .xmm2 .xmm2 0x4e, shuf .xmm3 .xmm3 0x93]

def doubleRound : Prog isa := .block (vhalf .xmm1 .xmm2 .xmm3 ++ toRows ++ vhalf .xmm3 .xmm2 .xmm1 ++ toCols)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- The doublewords of `xmm0, xmm1, xmm2` and `d` transposed in place, through
`t₀, …, t₃`. -/
def transpose (d t₀ t₁ t₂ t₃ : XReg) : List Instr :=
  [xb .movdqa t₀ .xmm0, xb .punpckldq t₀ .xmm1, xb .movdqa t₁ .xmm0, xb .punpckhdq t₁ .xmm1,
   xb .movdqa t₂ .xmm2, xb .punpckldq t₂ d, xb .movdqa t₃ .xmm2, xb .punpckhdq t₃ d,
   xb .movdqa .xmm0 t₀, xb .punpcklqdq .xmm0 t₂, xb .movdqa .xmm1 t₀, xb .punpckhqdq .xmm1 t₂,
   xb .movdqa .xmm2 t₁, xb .punpcklqdq .xmm2 t₃, xb .movdqa d t₁, xb .punpckhqdq d t₃]

/-- Loading `b`'s address and its four rows. -/
def load : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .eax 16),
   .movdquLoad .xmm2 (at_ .eax 32), .movdquLoad .xmm3 (at_ .eax 48)]

/-- From the rows to the columns: row `k` rotated by `k` doublewords, the
matrix transposed (`xmm0` holds the diagonal, `xmm1, xmm2, xmm3` the other
columns rotated by one, two and three doublewords), and those rotated back. -/
def toDiag : List Instr :=
  [shuf .xmm1 .xmm1 0x39, shuf .xmm2 .xmm2 0x4e, shuf .xmm3 .xmm3 0x93] ++
    transpose .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++
  [shuf .xmm4 .xmm3 0x39, shuf .xmm2 .xmm2 0x4e, shuf .xmm3 .xmm1 0x93, xb .movdqa .xmm1 .xmm4]

/-- `toDiag` undone, the rows into `xmm0, xmm1, xmm2, xmm4`. -/
def fromDiag : List Instr :=
  [shuf .xmm4 .xmm1 0x93, shuf .xmm1 .xmm3 0x39, shuf .xmm2 .xmm2 0x4e] ++
    transpose .xmm4 .xmm3 .xmm5 .xmm6 .xmm7 ++
  [shuf .xmm1 .xmm1 0x93, shuf .xmm2 .xmm2 0x4e, shuf .xmm4 .xmm4 0x39]

/-- The rows of the result (in `xmm0, xmm1, xmm2, xmm4`) plus those of the
input, into `b`. -/
def addRows : List Instr :=
  [.movdquLoad .xmm3 (at_ .eax 0), .movdquLoad .xmm5 (at_ .eax 16), .movdquLoad .xmm6 (at_ .eax 32),
   .movdquLoad .xmm7 (at_ .eax 48), xb .paddd .xmm0 .xmm3, xb .paddd .xmm1 .xmm5,
   xb .paddd .xmm2 .xmm6, xb .paddd .xmm4 .xmm7, .movdquStore (at_ .eax 0) .xmm0,
   .movdquStore (at_ .eax 16) .xmm1, .movdquStore (at_ .eax 32) .xmm2, .movdquStore (at_ .eax 48) .xmm4]

def finish : List Instr := fromDiag ++ addRows

def salsa : Prog isa := .seq (.block (load ++ toDiag)) (.seq (rounds 4) (.block finish))

end VG.Impl.Scrypt.X86
