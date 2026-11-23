module

public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.X86.Ecb

/-!
# Blowfish on x86 (32-bit) with its S-box look-ups by `pshufb`: sixteen blocks

`cryptBlocks`, the internal function `vg_blowfish_crypt_blocks16_ssse3`:
sixteen blocks encrypted, or decrypted, at once, for the functions that take
many blocks (ECB, CBC decryption, CFB64 decryption).

A look-up reads a plane's sixteen rows for the sixteen bytes of a register
at once (`Ssse3.lean`), so sixteen blocks take the loads of one: the halves
are four registers of four doublewords each, a round turns xL into four
registers of bytes, one of each byte of the sixteen xL (a `pshufb` a
register and a transposition of doublewords, `planes`), and for each S-box
makes the sixteen index vectors of its byte's register and reads its four
planes' rows (`Ssse3.index`, `Ssse3.scan`: the code of one block); the four
registers of the entries' bytes are turned back into doublewords the same
way (`entries`) and added or exclusive-ored into F (`combine`).

Its convention is its own: the sixteen blocks at the bytes 384 to 511 of
the working space at `edi`, of which it writes the bytes 64 to 767; the
schedule's address in `esi`; and in `edx` the address of the eighteen
entries of P in the order of use, so that the same code encrypts (the
schedule's P) and decrypts (a copy of it in reverse, which the decrypting
core writes at byte 768). The halves are at fixed offsets: a round keeps xL
after its entry of P in four places of its own, writes the new xL over the
old one and copies those places to xR. It keeps `esi`, `edi` and `esp`, and
uses eight bytes of stack.

`core16 up`: the function as a core of the modes for sixteen blocks, in
either direction; the modes take the groups of 16, 8, 4 and 2 blocks, then
one, each one run of it.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86.Ssse3.Wide

open VG.X86
open VG.Impl.Modes.X86 (sb argOp Core)
open VG.Impl.Modes (Mode)

/-- The internal function's name. -/
def fnName : String := "vg_blowfish_crypt_blocks16_ssse3"

/-! ## The working space's offsets -/

/-- The sixteen blocks. -/
def bufOff : Nat := 384
/-- xL of the blocks `4g` to `4g + 3`. -/
def xlOff (g : Nat) : Nat := 512 + 16 * g
/-- xR. -/
def xrOff (g : Nat) : Nat := 576 + 16 * g
/-- xL after the round's entry of P. -/
def tOff (g : Nat) : Nat := 640 + 16 * g
/-- Byte `b` of the sixteen xL. -/
def ioOff (b : Nat) : Nat := 704 + 16 * b
/-- P in reverse, for decryption. -/
def prOff : Nat := 768

/-! ## The blocks in and out -/

/-- The blocks `4g` to `4g + 3` to their halves, as big-endian doublewords. -/
def blockIn (g : Nat) : List Instr :=
  [ld .xmm0 .edi (bufOff + 32 * g), ld .xmm1 .edi (bufOff + 32 * g + 16), x .movdqa .xmm2 .xmm0,
   x .movdqa .xmm3 .xmm1, x .pshufb .xmm0 .xmm6, x .pshufb .xmm1 .xmm6, x .punpcklqdq .xmm0 .xmm1,
   x .pshufb .xmm2 .xmm7, x .pshufb .xmm3 .xmm7, x .punpcklqdq .xmm2 .xmm3, stx .edi (xlOff g) .xmm0,
   stx .edi (xrOff g) .xmm2]

def blocksIn : List Instr := ([tb .xmm6 oKL, tb .xmm7 oKR] : List Instr) ++ (List.range 4).flatMap blockIn

/-- The blocks `4g` to `4g + 3` from the halves after the last round: the
last exchange undone, with the last two entries of P in `xmm6` and `xmm7`. -/
def blockOut (g : Nat) : List Instr :=
  [ld .xmm0 .edi (xrOff g), x .pxor .xmm0 .xmm7, ld .xmm1 .edi (xlOff g), x .pxor .xmm1 .xmm6,
   x .movdqa .xmm2 .xmm0, x .punpckldq .xmm0 .xmm1, x .punpckhdq .xmm2 .xmm1, x .pshufb .xmm0 .xmm5,
   x .pshufb .xmm2 .xmm5, stx .edi (bufOff + 32 * g) .xmm0, stx .edi (bufOff + 32 * g + 16) .xmm2]

def blocksOut : List Instr :=
  ([.mov .eax (.mem (at_ .edx 0)), .xop (.movd .xmm6 .eax), .xop (.pshufd .xmm6 .xmm6 0),
    .mov .eax (.mem (at_ .edx 4)), .xop (.movd .xmm7 .eax), .xop (.pshufd .xmm7 .xmm7 0), tb .xmm5 oBS] :
    List Instr) ++ (List.range 4).flatMap blockOut

/-! ## A round -/

/-- The four doublewords of each of `a0` to `a3` transposed, with four other
registers: doubleword `k` of row `b` is doubleword `b` of `a k`; the rows
are in `a0`, `u0`, `t0` and `u1`. -/
def transpose (a0 a1 a2 a3 t0 t1 u0 u1 : XReg) : List Instr :=
  [x .movdqa t0 a0, x .punpckldq a0 a1, x .punpckhdq t0 a1, x .movdqa t1 a2, x .punpckldq a2 a3,
   x .punpckhdq t1 a3, x .movdqa u0 a0, x .punpcklqdq a0 a2, x .punpckhqdq u0 a2, x .movdqa u1 t0,
   x .punpcklqdq t0 t1, x .punpckhqdq u1 t1]

/-- xL of the blocks `4g` to `4g + 3` exclusive-ored with the round's entry
of P (in `xmm4`), to its place, and its bytes gathered by their number. -/
def xorP (g : Nat) : List Instr :=
  [ld (xr g) .edi (xlOff g), x .pxor (xr g) .xmm4, stx .edi (tOff g) (xr g), x .pshufb (xr g) .xmm5]

/-- `xL ^= P` for the entry at `edx`, and the four registers of the bytes of
the sixteen xL, to the working space. -/
def planes : List Instr :=
  ([.mov .eax (.mem (at_ .edx 0)), .xop (.movd .xmm4 .eax), .xop (.pshufd .xmm4 .xmm4 0), tb .xmm5 oT] :
    List Instr) ++ (List.range 4).flatMap xorP ++
    transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++
    [stx .edi (ioOff 0) .xmm0, stx .edi (ioOff 1) .xmm6, stx .edi (ioOff 2) .xmm4, stx .edi (ioOff 3) .xmm7]

/-- The nibbles of the bytes that index S-box `j` (byte `3 - j` of the
sixteen xL), in `xmm1` and `xmm0`. -/
def nibbles (j : Nat) : List Instr :=
  [ld .xmm0 .edi (ioOff (3 - j)), tb .xmm2 oM, x .movdqa .xmm1 .xmm0, .xop (.shift .psrld .xmm1 4),
   x .pand .xmm1 .xmm2, x .pand .xmm0 .xmm2]

/-- The register of an S-box's entries for the blocks `4g` to `4g + 3`. -/
def rw (g : Nat) : XReg :=
  match g with
  | 0 => .xmm4 | 1 => .xmm2 | 2 => .xmm0 | _ => .xmm3

/-- The four planes' bytes for the sixteen blocks (`xmm4` to `xmm7`) to the
entries of the blocks, four a register (`rw`). -/
def entries : List Instr :=
  transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm0 .xmm1 .xmm2 .xmm3 ++
    [tb .xmm5 oT, x .pshufb .xmm4 .xmm5, x .pshufb .xmm2 .xmm5, x .pshufb .xmm0 .xmm5, x .pshufb .xmm3 .xmm5]

/-- F's accumulation of S-box `j` for the blocks `4g` to `4g + 3`: S₁, then
+ S₂, XOR S₃, + S₄; and with S₄ the new xL, F exclusive-ored with xR. -/
def combine (j g : Nat) : List Instr :=
  if j = 0 then [stx .edi (fOff g) (rw g)]
  else if j = 3 then
    [ld .xmm6 .edi (fOff g), x .paddd (rw g) .xmm6, ld .xmm6 .edi (xrOff g), x .pxor (rw g) .xmm6,
     stx .edi (xlOff g) (rw g)]
  else [ld .xmm6 .edi (fOff g), x (if j = 2 then .pxor else .paddd) (rw g) .xmm6, stx .edi (fOff g) (rw g)]

/-- S-box `j` of the sixteen blocks, into F. -/
def sbox (j : Nat) : List Instr :=
  nibbles j ++ (List.range 16).flatMap index ++ scan j ++ entries ++ (List.range 4).flatMap (combine j)

/-- xL after the entry of P to xR. -/
def toR (g : Nat) : List Instr := [ld .xmm0 .edi (tOff g), stx .edi (xrOff g) .xmm0]

/-- A round of the sixteen blocks, and the next entry of P; the flags say
whether it was the sixteenth round's. -/
def round : List Instr :=
  planes ++ sbox 0 ++ sbox 1 ++ sbox 2 ++ sbox 3 ++ (List.range 4).flatMap toR ++
    [.alu .add .edx (imm 4), .alu .cmp .edx (.reg .ebp)]

/-- The table's address, and the end of the rounds' entries of P. -/
def start : List Instr := [.mov tbr (.reg .eax), .mov .ebp (.reg .edx), .alu .add .ebp (imm 64)]

/-- `vg_blowfish_crypt_blocks16_ssse3`: the sixteen blocks at byte 384 of
the working space at `edi`, under the schedule at `esi` with the entries of
P at `edx`. -/
def cryptBlocks : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block (start ++ blocksIn)) (.seq (.loop (.block round) .ne) (.block blocksOut)))

/-! ## The modes' core -/

/-- Entry `17 - i` of the schedule's P to place `i` of the copy. -/
def revP (i : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (pOff + 4 * (17 - i)))), .store (at_ sb (prOff + 4 * i)) .eax]

/-- The entries of P in the order of use, at `edx`. -/
def pSetup (up : Bool) : List Instr :=
  if up then [.mov .edx (.reg .esi), .alu .add .edx (imm pOff)]
  else (List.range 18).flatMap revP ++ [.mov .edx (.reg sb), .alu .add .edx (imm prOff)]

/-- The sixteen blocks of the core's buffer, encrypted (`up`) or decrypted in
place. -/
def crypt (up : Bool) : Prog isa :=
  .seq (.block (.mov .esi (.mem (argOp 0)) :: pSetup up)) (.call fnName cryptBlocks)

/-- The modes' core: sixteen blocks at a time, in either direction. Its
slots are the function's working space, the buffer in it. -/
def core16 (up : Bool) : Core :=
  { prepare := .block [], crypt := crypt up, slots := 212, total := 222, buf := 96, G := 16, bw := 2, stack := 8 }

/-- The sizes of the groups of blocks a mode takes in turn, before the
blocks left one at a time. -/
def levels : List Nat := [16, 8, 4, 2]

/-- ECB, with its scratch buffer as the fourth argument. -/
def ecb (up : Bool) : Prog isa := (core16 up).ecbLevels levels

/-- CBC decryption that updates the chaining value. -/
def cbcDecryptChained : Prog isa :=
  (core16 false).seqLevels (Mode.cbcDecWide 2) levels (Mode.cbcDecChained 2)

/-- CFB64 decryption. -/
def cfbDecrypt : Prog isa := (core16 true).seqLevels (Mode.cfbDecWide 2) levels (Mode.cfbDecEarly 2)

end VG.Impl.Blowfish.X86.Ssse3.Wide
