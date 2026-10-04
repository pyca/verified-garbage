import VerifiedGarbage.TCB.X86.State

/-!
# IA-32 MMX instructions

**Trusted.** Intel SDM Vol. 2, the forms of the named instructions on the
64-bit MMX registers (`mm0`–`mm7`), and the two SSE2 moves between them and
the XMM registers. They are MMX instructions, apart from PADDQ on MMX
registers, MOVQ2DQ and MOVDQ2Q, which are SSE2: all in this target's i686
baseline. None changes the flags or a general-purpose register.

Every one of them, but EMMS, makes the x87 tag word all valid (SDM Vol. 1
§9.5.1); EMMS empties it. The model has no x87 instructions, so it tracks
this only as whether the code is inside an MMX frame (`State.mmx`, see
`TCB/X86/Isa.lean`): these instructions fault outside one.
-/

namespace VG.X86

/-- A source of a two-operand MMX instruction: a register or a 64-bit
memory operand (`mm/m64`, which needs no alignment). -/
inductive MSrc
  | reg (r : MReg)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

/-- Two-operand MMX instructions `op mm, mm/m64` whose result is a function
of the destination's and the source's 64 bits. -/
inductive MBinOp | paddq | pxor | por | pand | pandn
  deriving DecidableEq, Repr

/-- Quadword shifts by an immediate count. -/
inductive MShiftOp | psllq | psrlq
  deriving DecidableEq, Repr

/-- MMX instructions that write only an MMX or XMM register. -/
inductive MOp
  /-- `op mm, mm/m64` -/
  | bin (op : MBinOp) (dst : MReg) (src : MSrc)
  /-- `op mm, imm8` -/
  | shift (op : MShiftOp) (dst : MReg) (count : BitVec 8)
  /-- `movq mm, mm` (NP 0F 6F /r), and from memory (`movq mm, m64`) -/
  | movq (dst : MReg) (src : MSrc)
  /-- `punpckldq mm, mm` (NP 0F 62 /r, register form) -/
  | punpckldq (dst src : MReg)
  /-- `movd mm, r32` (NP 0F 6E /r) -/
  | movd (dst : MReg) (src : Reg)
  /-- `movq2dq xmm, mm` (F3 0F D6 /r) -/
  | movq2dq (dst : XReg) (src : MReg)
  /-- `movdq2q mm, xmm` (F2 0F D6 /r) -/
  | movdq2q (dst : MReg) (src : XReg)
  deriving DecidableEq, Repr

/-- SDM Vol. 2, the MMX forms (no flags are affected):

* PADDQ (NP 0F D4 /r): `DEST[63:0] := DEST[63:0] + SRC[63:0]` (wrapping).
* PXOR (NP 0F EF /r): `DEST := DEST XOR SRC`. POR (NP 0F EB /r): `DEST :=
  DEST OR SRC`. PAND (NP 0F DB /r): `DEST := DEST AND SRC`. PANDN (NP 0F DF
  /r): `DEST := NOT(DEST) AND SRC`. -/
def MBinOp.eval : MBinOp → BitVec 64 → BitVec 64 → BitVec 64
  | .paddq, a, b => a + b
  | .pxor, a, b => a ^^^ b
  | .por, a, b => a ||| b
  | .pand, a, b => a &&& b
  | .pandn, a, b => ~~~a &&& b

/-- SDM Vol. 2, "PSLLW/PSLLD/PSLLQ" (NP 0F 73 /6 ib) and "PSRLW/PSRLD/PSRLQ"
(NP 0F 73 /2 ib), quadword, 64-bit operand: `IF (COUNT > 63) THEN DEST[63:0]
:= 0 ELSE DEST := ZeroExtend(DEST << COUNT)` (respectively `>>`, a logical
shift). -/
def MShiftOp.eval (op : MShiftOp) (a : BitVec 64) (count : BitVec 8) : BitVec 64 :=
  let n := count.toNat
  if 63 < n then 0 else match op with
    | .psllq => a <<< n
    | .psrlq => a >>> n

/-- The value of an MMX source, faulting outside the readable regions. -/
def MSrc.read (s : State) : MSrc → Option (BitVec 64)
  | .reg r => some (s.mm r)
  | .mem m =>
    let a := s.ea m
    if InRegions (s.rd ++ s.wr) a 8 then some (s.mem.readW a 64) else none

/-- The addresses an MMX source reads. -/
def MSrc.addrs (s : State) : MSrc → List Addr
  | .reg _ => []
  | .mem m => [s.ea m]

/-- SDM Vol. 2 (no flags are affected):

* MOVQ (NP 0F 6F /r, `MOVQ mm, mm/m64`): `DEST := SRC`.
* PUNPCKLDQ (NP 0F 62 /r, `PUNPCKLDQ mm, mm/m32`, register form):
  `DEST[63:32] := SRC[31:0]; DEST[31:0] := DEST[31:0]`.
* MOVD (NP 0F 6E /r, `MOVD mm, r/m32`): `DEST[31:0] := SRC; DEST[63:32] :=
  00000000H`.
* MOVQ2DQ (F3 0F D6 /r): `DEST[63:0] := SRC[63:0]; DEST[127:64] :=
  00000000000000000H`.
* MOVDQ2Q (F2 0F D6 /r): `DEST := SRC[63:0]`.

Each faults outside an MMX frame (`State.mmx`), and the memory forms outside
the readable regions. -/
def MOp.exec : MOp → State → Option State
  | .bin op d src, s => if s.mmx then (src.read s).map fun v => s.setMm d (op.eval (s.mm d) v) else none
  | .shift op d n, s => if s.mmx then some (s.setMm d (op.eval (s.mm d) n)) else none
  | .movq d src, s => if s.mmx then (src.read s).map fun v => s.setMm d v else none
  | .punpckldq d r, s =>
    if s.mmx then some (s.setMm d ((s.mm r).extractLsb' 0 32 ++ (s.mm d).extractLsb' 0 32)) else none
  | .movd d r, s => if s.mmx then some (s.setMm d ((0 : BitVec 32) ++ s.gpr r)) else none
  | .movq2dq d r, s => if s.mmx then some (s.setXmm d ((0 : BitVec 64) ++ s.mm r)) else none
  | .movdq2q d r, s => if s.mmx then some (s.setMm d ((s.xmm r).extractLsb' 0 64)) else none

/-- The addresses an MMX instruction reads. -/
def MOp.addrs : MOp → State → List Addr
  | .bin _ _ src, s | .movq _ src, s => src.addrs s
  | _, _ => []

end VG.X86
