module

public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.TCB.X86.Isa

/-! # Constant-time RC2 selection on baseline x86

Every candidate is visited in order. Secret indices affect arithmetic masks,
never addresses or branches. The three-register PITABLE lookup leaves the
public key-expansion counters and pointers intact.
-/

@[expose] public section

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

`keyLookup r` selects word `i = r & 63` of the schedule at EDI into the low
half of ESI. The schedule's 128 bytes are eight rows of 16 bytes: bits 5, 4
and 3 of `i` choose one of them by a tree of selections (`pick`), and bits 2,
1 and 0 then shift it by 8, 4 and 2 bytes, or not (`slide`), which leaves the
word in its low 16 bits. Every row is loaded, at a fixed address, and the
masks are made from the bits of `r` in `xmm7`, whose bits 6 and up do not
matter. The word passes through the 8 bytes at `[ebp + 48]`. -/

/-- The low half of `r` in every word of `xmm7`. -/
def idxWords (r : Reg) : List Instr :=
  [.xop (.movd .xmm7 r), .xop (.pshuflw .xmm7 .xmm7 0), .xop (.bin .punpcklqdq .xmm7 .xmm7)]

/-- `xmm6 := ` all ones if bit `b` of the index is 1, or nothing. -/
def idxMask (b : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm6 .xmm7), .xop (.shift .pslld .xmm6 (BitVec.ofNat 8 (15 - b))),
   .xop (.shift .psraw .xmm6 15)]

/-- `d := s` where `xmm6` is all ones; `s` is overwritten. -/
def pick (d s : XReg) : List Instr :=
  [.xop (.bin .pxor s d), .xop (.bin .pand s .xmm6), .xop (.bin .pxor d s)]

/-- Row `c`, or row `c + 4`, into `d`, through `t`. -/
def pickRow (c : Nat) (d t : XReg) : List Instr :=
  ([.movdquLoad d (memOp .edi (16 * c)), .movdquLoad t (memOp .edi (16 * (c + 4)))] : List Instr) ++ pick d t

/-- `xmm0` shifted right by `n` bytes if bit `b` of the index is 1. -/
def slide (b n : Nat) : List Instr :=
  idxMask b ++ ([.xop (.bin .movdqa .xmm1 .xmm0), .xop (.shift .psrldq .xmm1 (BitVec.ofNat 8 n))] : List Instr) ++
    pick .xmm0 .xmm1

/-- Row `(r & 63) >> 3` into `xmm0`. -/
def pickRows : List Instr :=
  idxMask 5 ++ pickRow 0 .xmm0 .xmm4 ++ pickRow 1 .xmm1 .xmm5 ++ pickRow 2 .xmm2 .xmm4 ++ pickRow 3 .xmm3 .xmm5 ++
  idxMask 4 ++ pick .xmm0 .xmm2 ++ pick .xmm1 .xmm3 ++ idxMask 3 ++ pick .xmm0 .xmm1

/-- Word `(r & 63) & 7` of the row in `xmm0` into its low 16 bits. -/
def slides : List Instr := slide 2 8 ++ slide 1 4 ++ slide 0 2

/-- `xmm0`'s low doubleword into ESI, through `[ebp + 48]`. -/
def lookEnd : List Instr := [.movqStore (memOp .ebp 48) .xmm0, .mov .esi (.mem (memOp .ebp 48))]

/-- Select schedule[`r` & 63] from EDI into the low half of ESI; clobbers
`xmm0`–`xmm7` and the 8 bytes at `[ebp + 48]`. -/
def keyLookup (r : Reg) : List Instr := idxWords r ++ pickRows ++ slides ++ lookEnd

end VG.Impl.Rc2.X86
