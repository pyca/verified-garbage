module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.X86.Ecb
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# CAST5 on x86 (32-bit) with its S-box look-ups by `pshufb`: sixteen blocks

`cryptBlocks`, the internal function `vg_cast5_crypt_blocks16_ssse3`:
sixteen blocks encrypted, or decrypted, at once, for the functions that take
many blocks (ECB, CBC decryption, CFB64 decryption).

A look-up reads a plane's sixteen rows for the sixteen bytes of a register
at once (`Ssse3.lean`), so sixteen blocks take the loads of one: the halves
are four registers of four doublewords each. A round makes `I` of the
sixteen blocks in four registers (`mix`: `Km + D`, `Km ^ D` or `Km - D` by
the round's type), rotates them by `Kr` in five steps, each kept or not
under a mask of `Kr`'s bit (`rotate`, the baseline's steps on vectors),
turns them into four registers of bytes, one of each byte of the sixteen
`I` (a `pshufb` a register and a transposition of doublewords, `planes`),
and for each S-box makes the sixteen index vectors of its byte's register
and reads its four planes' rows (`Ssse3.index`, `Ssse3.scan`: the code of
one block); the four registers of the entries' bytes are turned back into
doublewords the same way (`entries`), and the four S-boxes' entries are
combined by the round's type (`comb`) and exclusive-ored into the other
half.

One loop runs the rounds, in either direction: the round's number is in the
working space, with the step to the next (1 or -1) and the count of rounds
left, all public. Its type, the number modulo 3, is computed from it
(`roundType`), and the code of `mix` and `comb` is chosen by a branch on
it; the rest of a round, the look-ups among it, is there once.

The function's convention is its own: the working space at `esi`, with the
sixteen blocks at its first 128 bytes, the round to start with (its number
less one), the step and the number of rounds at the bytes 256 to 267; the
subkeys' address in `ebp`. It writes the working space's bytes 0 to 847,
keeps `esi`, `edi`, `ebp` and `esp`, and uses eight bytes of stack.

`core16 up`: the function as a core of the modes for sixteen blocks, in
either direction; the modes take the groups of 16, 8, 4 and 2 blocks, then
one, each one run of it.

`Fn`: the functions as emitted, each with the working space, 888 bytes, in a
frame of its own that it zeroes on return: 916 bytes for ECB, which copies
four arguments, and 920 for CBC and CFB64 decryption, which copy five, so
that the working space is at a multiple of sixteen when `esp` was one at
the call. The ECB functions do not use the `scratch` that their `Api` gives
them.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86.Ssse3.Wide

open VG.X86
open VG.Impl.Cast5.X86
open VG.Impl.Modes.X86 (sb argOp Core)
open VG.Impl.Modes (Mode)

/-- The internal function's name. -/
def fnName : String := "vg_cast5_crypt_blocks16_ssse3"

/-! ## The working space's offsets -/

/-- The sixteen blocks. -/
def bufOff : Nat := 0
/-- `L` of the blocks `4g` to `4g + 3`. -/
def lOff (g : Nat) : Nat := 128 + 16 * g
/-- `R`. -/
def rOff (g : Nat) : Nat := 192 + 16 * g
/-- The round's number, less one. -/
def rnOff : Nat := 256
/-- The step to the next round's number. -/
def stOff : Nat := 260
/-- The rounds left. -/
def cnOff : Nat := 264
/-- Byte `b` of the sixteen `I`. -/
def ioOff (b : Nat) : Nat := 528 + 16 * b
/-- S-box `j`'s entries for the blocks `4g` to `4g + 3`. -/
def enOff (j g : Nat) : Nat := 592 + 64 * j + 16 * g

/-! ## The blocks in and out -/

/-- The blocks `4g` to `4g + 3` to their halves, as big-endian doublewords. -/
def blockIn (g : Nat) : List Instr :=
  [ld .xmm0 .esi (bufOff + 32 * g), ld .xmm1 .esi (bufOff + 32 * g + 16), x .movdqa .xmm2 .xmm0,
   x .movdqa .xmm3 .xmm1, x .pshufb .xmm0 .xmm6, x .pshufb .xmm1 .xmm6, x .punpcklqdq .xmm0 .xmm1,
   x .pshufb .xmm2 .xmm7, x .pshufb .xmm3 .xmm7, x .punpcklqdq .xmm2 .xmm3, stx .esi (lOff g) .xmm0,
   stx .esi (rOff g) .xmm2]

def blocksIn : List Instr := ([tb .xmm6 oKL, tb .xmm7 oKR] : List Instr) ++ (List.range 4).flatMap blockIn

/-- The blocks `4g` to `4g + 3` from the halves after the last round, `R`
first. -/
def blockOut (g : Nat) : List Instr :=
  [ld .xmm0 .esi (rOff g), ld .xmm1 .esi (lOff g), x .movdqa .xmm2 .xmm0, x .punpckldq .xmm0 .xmm1,
   x .punpckhdq .xmm2 .xmm1, x .pshufb .xmm0 .xmm5, x .pshufb .xmm2 .xmm5, stx .esi (bufOff + 32 * g) .xmm0,
   stx .esi (bufOff + 32 * g + 16) .xmm2]

def blocksOut : List Instr := ([tb .xmm5 oBS] : List Instr) ++ (List.range 4).flatMap blockOut

/-! ## A round -/

/-- The round's type in `ebx`: its number `i` modulo 3, as `i - 3 (11 i / 32)`
(`i` is at most 16); then `Km` in `eax` and `Kr` in `ecx`, and whether the
type is 1. -/
def roundType : List Instr :=
  [.mov .ebx (.mem (at_ .esi rnOff)), .alu .add .ebx (imm 1), .mov .eax (.reg .ebx), .mov .ecx (.reg .ebx),
   .alu .add .ecx (.reg .ecx), .alu .add .eax (.reg .ecx), .alu .add .ecx (.reg .ecx),
   .alu .add .ecx (.reg .ecx), .alu .add .eax (.reg .ecx), .shift .shr .eax 5, .mov .ecx (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx), .alu .sub .ebx (.reg .eax),
   .mov .eax (.mem (at_ .esi rnOff)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .ebp), .mov .ecx (.mem (at_ .eax 64)), .mov .eax (.mem (at_ .eax 0)),
   .alu .cmp .ebx (imm 1)]

/-- `Km` in every doubleword of `xmm7`. -/
def bcKm : List Instr := [.xop (.movd .xmm7 .eax), .xop (.pshufd .xmm7 .xmm7 0)]

/-- `I` before its rotation, of the blocks `4g` to `4g + 3`, in register
`g`: `Km + D` (type 1), `Km ^ D` (type 2). -/
def mixG (op : XBinOp) (g : Nat) : List Instr := [ld (xr g) .esi (rOff g), x op (xr g) .xmm7]

/-- `Km - D`, as `~D + (Km + 1)`. -/
def mixSub (g : Nat) : List Instr := [ld (xr g) .esi (rOff g), x .pxor (xr g) .xmm6, x .paddd (xr g) .xmm7]

/-- `I` before its rotation, by the round's type. -/
def mix : Nat → List Instr
  | 1 => bcKm ++ (List.range 4).flatMap (mixG .paddd)
  | 2 => bcKm ++ (List.range 4).flatMap (mixG .pxor)
  | _ => ([.alu .add .eax (imm 1)] : List Instr) ++ bcKm ++ [tb .xmm6 oOnes] ++ (List.range 4).flatMap mixSub

/-- Step `b` of the rotation of register `g`: by `2 ^ b`, kept under the
mask in `xmm6`. -/
def rotG (b g : Nat) : List Instr :=
  [x .movdqa .xmm4 (xr g), x .movdqa .xmm5 (xr g), .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 (2 ^ b))),
   .xop (.shift .psrld .xmm5 (BitVec.ofNat 8 (32 - 2 ^ b))), x .por .xmm4 .xmm5, x .pxor (xr g) .xmm4,
   x .pand (xr g) .xmm6, x .pxor (xr g) .xmm4]

/-- Step `b` of the rotation of the four registers by the low 5 bits of
`ecx` (shifted right by `b` so far): the mask is zero if bit 0 of `ecx` is
set, all ones if not. -/
def rotStep (b : Nat) : List Instr :=
  ([.mov .eax (.reg .ecx), .alu .and .eax (imm 1), .alu .sub .eax (imm 1), .xop (.movd .xmm6 .eax),
    .xop (.pshufd .xmm6 .xmm6 0)] : List Instr) ++ (List.range 4).flatMap (rotG b) ++
    (if b < 4 then [.shift .shr .ecx 1] else [])

def rotate : List Instr := (List.range 5).flatMap rotStep

/-- The four doublewords of each of `a0` to `a3` transposed, with four other
registers: doubleword `k` of row `b` is doubleword `b` of `a k`; the rows
are in `a0`, `u0`, `t0` and `u1`. -/
def transpose (a0 a1 a2 a3 t0 t1 u0 u1 : XReg) : List Instr :=
  [x .movdqa t0 a0, x .punpckldq a0 a1, x .punpckhdq t0 a1, x .movdqa t1 a2, x .punpckldq a2 a3,
   x .punpckhdq t1 a3, x .movdqa u0 a0, x .punpcklqdq a0 a2, x .punpckhqdq u0 a2, x .movdqa u1 t0,
   x .punpcklqdq t0 t1, x .punpckhqdq u1 t1]

/-- The four registers of the bytes of the sixteen `I`, to the working
space. -/
def planes : List Instr :=
  ([tb .xmm5 oT, x .pshufb .xmm0 .xmm5, x .pshufb .xmm1 .xmm5, x .pshufb .xmm2 .xmm5, x .pshufb .xmm3 .xmm5] :
    List Instr) ++ transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++
    [stx .esi (ioOff 0) .xmm0, stx .esi (ioOff 1) .xmm6, stx .esi (ioOff 2) .xmm4, stx .esi (ioOff 3) .xmm7]

/-- The nibbles of the bytes that index S-box `j` (byte `3 - j` of the
sixteen `I`), in `xmm1` and `xmm0`. -/
def nibbles (j : Nat) : List Instr :=
  [ld .xmm0 .esi (ioOff (3 - j)), tb .xmm2 oM, x .movdqa .xmm1 .xmm0, .xop (.shift .psrld .xmm1 4),
   x .pand .xmm1 .xmm2, x .pand .xmm0 .xmm2]

/-- The four planes' bytes for the sixteen blocks (`xmm4` to `xmm7`) to the
entries of the blocks, four a register (`xmm4`, `xmm2`, `xmm0` and `xmm3`),
to the working space. -/
def entries (j : Nat) : List Instr :=
  transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm0 .xmm1 .xmm2 .xmm3 ++
    [tb .xmm5 oT, x .pshufb .xmm4 .xmm5, x .pshufb .xmm2 .xmm5, x .pshufb .xmm0 .xmm5, x .pshufb .xmm3 .xmm5,
     stx .esi (enOff j 0) .xmm4, stx .esi (enOff j 1) .xmm2, stx .esi (enOff j 2) .xmm0,
     stx .esi (enOff j 3) .xmm3]

/-- S-box `j` of the sixteen blocks. -/
def sbox (j : Nat) : List Instr := nibbles j ++ (List.range 16).flatMap index ++ scan j ++ entries j

/-- The look-ups of a round, and whether its type is 1. -/
def lookups : List Instr :=
  rotate ++ planes ++ sbox 0 ++ sbox 1 ++ sbox 2 ++ sbox 3 ++ [.alu .cmp .ebx (imm 1)]

/-- An operation of `f` on register `a` with `xmm4`: exclusive or, a sum, or
a difference, as `a + ~b + 1` (`0xff` in every byte in `xmm6`, 1 in every
doubleword in `xmm7`). -/
def fOp (o : Nat) (a : XReg) : List Instr :=
  match o with
  | 0 => [x .pxor a .xmm4]
  | 1 => [x .paddd a .xmm4]
  | _ => [x .pxor .xmm4 .xmm6, x .paddd a .xmm4, x .paddd a .xmm7]

/-- `f` of the blocks `4g` to `4g + 3` from the four S-boxes' entries, with
the operations `o1`, `o2` and `o3`; then `(L, R) := (R, L ^ f)`. -/
def combG (o1 o2 o3 g : Nat) : List Instr :=
  [ld (xr g) .esi (enOff 0 g), ld .xmm4 .esi (enOff 1 g)] ++ fOp o1 (xr g) ++ [ld .xmm4 .esi (enOff 2 g)] ++
    fOp o2 (xr g) ++ [ld .xmm4 .esi (enOff 3 g)] ++ fOp o3 (xr g) ++
    [ld .xmm4 .esi (lOff g), x .pxor (xr g) .xmm4, ld .xmm5 .esi (rOff g), stx .esi (lOff g) .xmm5,
     stx .esi (rOff g) (xr g)]

/-- `f` and the halves' exchange, by the round's type: `((a ^ b) - c) + d`,
`((a - b) + c) ^ d` or `((a + b) ^ c) - d`. -/
def comb (t : Nat) : List Instr :=
  ([tb .xmm6 oOnes, tb .xmm7 oOne] : List Instr) ++
    (List.range 4).flatMap (match t with
      | 1 => combG 0 2 1
      | 2 => combG 2 1 0
      | _ => combG 1 0 2)

/-- The next round's number, and the count of rounds left down (ZF set at 0).
The step is added from a register: the taint analysis knows a doubleword of
the working space public where a `mov` loads it. -/
def next : List Instr :=
  [.mov .eax (.mem (at_ .esi rnOff)), .mov .ecx (.mem (at_ .esi stOff)), .alu .add .eax (.reg .ecx),
   .store (at_ .esi rnOff) .eax, .mov .eax (.mem (at_ .esi cnOff)), .alu .sub .eax (imm 1),
   .store (at_ .esi cnOff) .eax]

/-- Code by the round's type, which `ebx` holds, after its comparison with 1. -/
def byType (f : Nat → List Instr) : Prog isa :=
  .ite .e (.block (f 1)) (.seq (.block [.alu .cmp .ebx (imm 2)]) (.ite .e (.block (f 2)) (.block (f 3))))

/-- A round of the sixteen blocks. -/
def round : Prog isa :=
  .seq (.block roundType) (.seq (byType mix) (.seq (.block lookups) (.seq (byType comb) (.block next))))

/-- `vg_cast5_crypt_blocks16_ssse3`: the sixteen blocks at the working space
at `esi`, under the subkeys at `ebp`, by the rounds the working space
states. -/
def cryptBlocks : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block (([.mov tbr (.reg .eax)] : List Instr) ++ blocksIn))
      (.seq (.loop round .ne) (.block blocksOut)))

/-! ## The modes' core -/

/-- The rounds in order: from the first up, or from the last down. -/
def setup (up : Bool) : List Instr :=
  ([.mov .esi (.reg sb), .mov .ebp (.mem (argOp 0)), .mov .eax (.mem (argOp 1)), .store (at_ .esi cnOff) .eax] :
    List Instr) ++
    (if up then [.mov .eax (imm 0), .store (at_ .esi rnOff) .eax, .mov .eax (imm 1), .store (at_ .esi stOff) .eax]
     else [.alu .sub .eax (imm 1), .store (at_ .esi rnOff) .eax, .mov .eax (imm 0xFFFFFFFF),
       .store (at_ .esi stOff) .eax])

/-- The sixteen blocks of the core's buffer, encrypted (`up`) or decrypted in
place. -/
def crypt (up : Bool) : Prog isa := .seq (.block (setup up)) (.call fnName cryptBlocks)

/-- The modes' core: sixteen blocks at a time, in either direction. Its
slots are the function's working space, the buffer at its start. -/
def core16 (up : Bool) : Core :=
  { prepare := .block [], crypt := crypt up, slots := 212, total := 222, buf := 0, G := 16, bw := 2, stack := 8,
    ka := 2 }

/-- The sizes of the groups of blocks a mode takes in turn, before the
blocks left one at a time. -/
def levels : List Nat := [16, 8, 4, 2]

/-- ECB, with its scratch buffer as the fifth argument. -/
def ecb (up : Bool) : Prog isa := (core16 up).ecbLevels levels

/-- CBC decryption that updates the chaining value. -/
def cbcDecryptChained : Prog isa :=
  (core16 false).seqLevels (Mode.cbcDecWide 2) levels (Mode.cbcDecChained 2)

/-- CFB64 decryption. -/
def cfbDecrypt : Prog isa := (core16 true).seqLevels (Mode.cfbDecWide 2) levels (Mode.cfbDecEarly 2)

/-! ## The functions as emitted -/

namespace Fn

/-- The doublewords of the 924 bytes of stack below `esp` that the residue
analysis finds an ECB function may leave different in two runs: the
sixteen-block function's return address and its table's address, the header
of the working space's frame, and the frame's last doubleword, which nothing
writes. -/
def ecbWords : List Nat := [1, 2, 3, 4, 5, 6, 7, 230]

/-- Those of the 928 bytes of CBC and CFB64 decryption. -/
def words : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 231]

/-- `Spec.Cast5.ecbEncryptApi`'s function as emitted: the working space is
its own, in a frame, and the caller's `scratch`, the fifth argument, is not
used. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 924 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 916 4 222 (ecb true))

/-- `Spec.Cast5.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 924 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 916 4 222 (ecb false))

/-- `Spec.Cast5.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 928 words (Impl.StackScratch.X86.withStackScratchWiped 920 5 222 Wide.cbcDecryptChained)

/-- `Spec.Cast5.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 928 words (Impl.StackScratch.X86.withStackScratchWiped 920 5 222 Wide.cfbDecrypt)

end Fn

end VG.Impl.Cast5.X86.Ssse3.Wide
