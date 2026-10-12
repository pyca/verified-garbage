import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.TCB.X86.Isa

/-! # Constant-time RC2 selection on baseline x86

Every candidate is visited in order. Secret indices affect arithmetic masks,
never addresses or branches. The three-register PITABLE lookup leaves the
public key-expansion counters and pointers intact.
-/

namespace VG.Impl.Rc2.X86

open VG.X86

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }
def rr (dst src : Reg) : Instr := .mov dst (.reg src)
def imm (dst : Reg) (n : Nat) : Instr := .mov dst (.imm (BitVec.ofNat 32 n))

/-! ## PITABLE, in SSE2 registers

`piLookup` leaves PITABLE[EAX & 255] in EAX without a table in memory: the
table's 64 little-endian dwords (`piWord`) are put into SSE2 registers from
immediates, four at a time, lane `k` of group `g` holding dword `4 g + k`,
and the one whose number is `i >> 2` survives its mask (as for the
schedule's words below). The lanes are ORed together, and the byte `i & 3`
of the dword is chosen in every lane by masks from bits 1 and 0 of `i`.
Lane 0 passes through the 16 bytes at EDI, whose contents are kept in
`xmm7` and stored back. -/

/-- PITABLE's bytes `4 j … 4 j + 3`, as a little-endian dword. -/
def piWord (j : Nat) : BitVec 32 :=
  (Spec.Rc2.piTable.getD (4 * j) 0).setWidth 32 |||
    (Spec.Rc2.piTable.getD (4 * j + 1) 0).setWidth 32 <<< 8 |||
    (Spec.Rc2.piTable.getD (4 * j + 2) 0).setWidth 32 <<< 16 |||
    (Spec.Rc2.piTable.getD (4 * j + 3) 0).setWidth 32 <<< 24

/-- `xmm0 := q = (EAX & 255) >> 2` in every lane, `EBX := EAX & 255`, the lane
numbers `0, 1, 2, 3` in `xmm2`, four in every lane of `xmm3`, all ones in
`xmm6`, nothing in `xmm1`; through EDX. -/
def piStart : List Instr :=
  [.alu .and .eax (.imm 255), rr .ebx .eax, .shift .shr .eax 2,
   .xop (.movd .xmm0 .eax), .xop (.pshufd .xmm0 .xmm0 0),
   imm .edx 1, .xop (.movd .xmm2 .edx), .xop (.pshufd .xmm2 .xmm2 0x11),
   imm .edx 2, .xop (.movd .xmm3 .edx), .xop (.pshufd .xmm3 .xmm3 0x05),
   .xop (.bin .paddd .xmm2 .xmm3),
   imm .edx 4, .xop (.movd .xmm3 .edx), .xop (.pshufd .xmm3 .xmm3 0),
   imm .edx 0xFFFFFFFF, .xop (.movd .xmm6 .edx), .xop (.pshufd .xmm6 .xmm6 0),
   .xop (.bin .pxor .xmm1 .xmm1)]

/-- Dwords `4 g … 4 g + 3` of the table `w` (PITABLE's, `piWord`) into
`xmm5`, through EDX, `xmm4` and `xmm7`. -/
def piLanes (w : Nat → BitVec 32) (g : Nat) : List Instr :=
  [.mov .edx (.imm (w (4 * g))), .xop (.movd .xmm5 .edx),
   .mov .edx (.imm (w (4 * g + 1))), .xop (.movd .xmm7 .edx), .xop (.bin .punpckldq .xmm5 .xmm7),
   .mov .edx (.imm (w (4 * g + 2))), .xop (.movd .xmm4 .edx),
   .mov .edx (.imm (w (4 * g + 3))), .xop (.movd .xmm7 .edx), .xop (.bin .punpckldq .xmm4 .xmm7),
   .xop (.bin .punpcklqdq .xmm5 .xmm4)]

/-- Group `g`: its dwords, each masked by whether its number (in `xmm2`) is
`q`, ORed into `xmm1`; then the next four numbers. -/
def piGroup (w : Nat → BitVec 32) (g : Nat) : List Instr :=
  piLanes w g ++
  [.xop (.bin .movdqa .xmm4 .xmm0), .xop (.bin .pxor .xmm4 .xmm2), .xop (.bin .paddd .xmm4 .xmm6),
   .xop (.shift .psrld .xmm4 8), .xop (.bin .movdqa .xmm7 .xmm4), .xop (.shift .pslld .xmm7 8),
   .xop (.bin .por .xmm4 .xmm7),
   .xop (.bin .pand .xmm5 .xmm4), .xop (.bin .por .xmm1 .xmm5), .xop (.bin .paddd .xmm2 .xmm3)]

/-- `-(bit n of EBX)` in every lane of `x`, through EDX. -/
def bitMask (x : XReg) (n : Nat) : List Instr :=
  [rr .edx .ebx] ++ (if n = 0 then [] else [.shift .shr .edx n]) ++
  [.alu .and .edx (.imm 1), .alu .xor .edx (.imm 0xFFFFFFFF), .alu .add .edx (.imm 1),
   .xop (.movd x .edx), .xop (.pshufd x x 0)]

/-- `xmm1 := xmm1 >> n` in the lanes where `x` is all ones (`v ^ ((v ^ (v >> n)) & m)`),
through `xmm4`. -/
def shiftIf (x : XReg) (n : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm4 .xmm1), .xop (.shift .psrld .xmm4 (BitVec.ofNat 8 n)),
   .xop (.bin .pxor .xmm4 .xmm1), .xop (.bin .pand .xmm4 x), .xop (.bin .pxor .xmm1 .xmm4)]

/-- The lanes ORed together (into every lane), the byte `EBX & 3` of the
dword chosen, and lane 0 to EAX through the 16 bytes at EDI, which are kept
in `xmm7` and stored back. -/
def piEnd : List Instr :=
  [.xop (.pshufd .xmm4 .xmm1 0x4E), .xop (.bin .por .xmm1 .xmm4),
   .xop (.pshufd .xmm4 .xmm1 0xB1), .xop (.bin .por .xmm1 .xmm4)] ++
  bitMask .xmm2 1 ++ shiftIf .xmm2 16 ++ bitMask .xmm3 0 ++ shiftIf .xmm3 8 ++
  [.movdquLoad .xmm7 (memOp .edi 0), .movdquStore (memOp .edi 0) .xmm1,
   .mov .eax (.mem (memOp .edi 0)), .movdquStore (memOp .edi 0) .xmm7,
   .alu .and .eax (.imm 255)]

/-- Select entry `EAX & 255` of the table of dwords `w`. -/
def piLookupWith (w : Nat → BitVec 32) : List Instr :=
  piStart ++ (List.range 16).flatMap (piGroup w) ++ piEnd

/-- Select PITABLE[EAX & 255]; clobbers EAX, EBX, EDX, `xmm0`–`xmm7` and
flags, and needs the 16 bytes at EDI readable and writable. -/
def piLookup : List Instr := piLookupWith piWord

/-! ## The schedule's words, in SSE2 registers

`keyLookup` selects word `i = EAX & 63` of the schedule at EDI from its 32
dwords, four at a time: dword `d = i >> 1` is the one whose number, in its
lane of `xmm2` (`4 c + k` in lane `k` of chunk `c`), equals `d` broadcast in
`xmm0`. The model's SSE2 has no `pcmpeqd`, so the mask is built from
`x = d ^ (4 c + k)`, which is below 256: `x - 1` shifted right by 8 is
`0x00FFFFFF` if `x = 0` and `0` otherwise, and ORed with itself shifted left
by 8 it is all ones or nothing (as for CAST5, `Impl/Cast5/X86.lean`). The
lanes ORed are stored at `[ebp + 48]` and ORed together into EAX; bit 0 of
`i` then chooses its half. -/

/-- `xmm0 := d = (EAX & 63) >> 1` in every lane, `EBX := EAX & 63`, the lane
numbers `0, 1, 2, 3` in `xmm2`, four in every lane of `xmm3`, all ones in
`xmm6`, nothing in `xmm1`; through ECX. -/
def lookStart : List Instr :=
  [.alu .and .eax (.imm 63), rr .ebx .eax, .shift .shr .eax 1,
   .xop (.movd .xmm0 .eax), .xop (.pshufd .xmm0 .xmm0 0),
   imm .ecx 1, .xop (.movd .xmm2 .ecx), .xop (.pshufd .xmm2 .xmm2 0x11),
   imm .ecx 2, .xop (.movd .xmm3 .ecx), .xop (.pshufd .xmm3 .xmm3 0x05),
   .xop (.bin .paddd .xmm2 .xmm3),
   imm .ecx 4, .xop (.movd .xmm3 .ecx), .xop (.pshufd .xmm3 .xmm3 0),
   imm .ecx 0xFFFFFFFF, .xop (.movd .xmm6 .ecx), .xop (.pshufd .xmm6 .xmm6 0),
   .xop (.bin .pxor .xmm1 .xmm1)]

/-- Dwords `4 c … 4 c + 3` of the schedule: each masked by whether its number
(in `xmm2`) is `d`, and ORed into `xmm1`; then the next four numbers. -/
def lookChunk (c : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm4 .xmm0), .xop (.bin .pxor .xmm4 .xmm2), .xop (.bin .paddd .xmm4 .xmm6),
   .xop (.shift .psrld .xmm4 8), .xop (.bin .movdqa .xmm7 .xmm4), .xop (.shift .pslld .xmm7 8),
   .xop (.bin .por .xmm4 .xmm7),
   .movdquLoad .xmm5 (memOp .edi (16 * c)), .xop (.bin .pand .xmm5 .xmm4),
   .xop (.bin .por .xmm1 .xmm5), .xop (.bin .paddd .xmm2 .xmm3)]

/-- Dword `d` (the OR of the lanes of `xmm1`, through `[ebp + 48]`), then its
half chosen by bit 0 of EBX: `EAX := (D >> 16) & m | D & ~m & 0xFFFF` for
`m = -(EBX & 1)`; through ECX. -/
def lookEnd : List Instr :=
  [.movdquStore (memOp .ebp 48) .xmm1, .mov .eax (.mem (memOp .ebp 48)),
   .alu .or .eax (.mem (memOp .ebp 52)), .alu .or .eax (.mem (memOp .ebp 56)),
   .alu .or .eax (.mem (memOp .ebp 60)),
   .alu .and .ebx (.imm 1), .alu .xor .ebx (.imm 0xffffffff), .alu .add .ebx (.imm 1),
   rr .ecx .eax, .shift .shr .ecx 16, .alu .and .ecx (.reg .ebx),
   .alu .xor .ebx (.imm 0xffffffff), .alu .and .eax (.reg .ebx), .alu .and .eax (.imm 65535),
   .alu .or .eax (.reg .ecx)]

/-- Select schedule[EAX & 63] from EDI; clobbers EAX, EBX, ECX, `xmm0`–`xmm7`,
the flags and the 16 bytes at `[ebp + 48]`. -/
def keyLookup : List Instr :=
  lookStart ++ (List.range 8).flatMap lookChunk ++ lookEnd

end VG.Impl.Rc2.X86
