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

/-- Equality mask for the low byte in EAX, returned in EDX. -/
def selectMask (i : Nat) : List Instr :=
  [rr .edx .eax, .alu .xor .edx (.imm (BitVec.ofNat 32 i)),
   .alu .sub .edx (.imm 1), .shift .shr .edx 31,
   .alu .xor .edx (.imm 0xffffffff), .alu .add .edx (.imm 1)]

def piStep (i : Nat) : List Instr :=
  selectMask i ++
    ([.alu .and .edx (.imm ((Spec.Rc2.piTable.getD i 0).setWidth 32)),
      .alu .or .ebx (.reg .edx)] : List Instr)

/-- Select PITABLE[EAX & 255]; clobbers EAX, EBX, EDX and flags. -/
def piLookup : List Instr :=
  ([.alu .and .eax (.imm 255), imm .ebx 0] : List Instr) ++
    (List.range 256).flatMap piStep ++ ([rr .eax .ebx] : List Instr)

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
