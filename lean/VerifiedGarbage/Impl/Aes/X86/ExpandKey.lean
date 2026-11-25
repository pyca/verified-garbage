module

public import VerifiedGarbage.Impl.Aes.X86.Ctr32

/-!
# AES key expansion on x86 (32-bit): `vg_aes_expand_key_scratch`

`vg_aes_expand_key_scratch(key, key_len, schedule, scratch)`, cdecl (every
argument on the stack): the key is copied to the schedule, then each further
word is made from the one before it, at `esi`, and the one `Nk` words back.

SUBWORD (`subWordCode`) is bitsliced, of the one word in `eax`, without a
transposition: slice `j` is the word shifted right by `j`, whose bits 0, 8, 16
and 24 are bit `j` of the four bytes; the circuit works on every bit, so what
the others are does not matter (`slices`). The S-box without its constant,
`subSlices`, is in an order and an allocation that take few instructions;
`gather` then adds up `(slice j & 0x01010101) << j` from the highest slice
down, and the constant `{63}` is added to the four bytes.

The counters are in the scratch buffer (at `edi`), after the saved registers:
the round constant (`rcOff`), four times the word's index in its group of
`Nk` (`jmOff`), `4 Nk` (`nkOff`) and the words left (`leftOff`).
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86

/-! ## SUBWORD -/

/-- Bit 0 of each byte. -/
def bit0 (d : Reg) : Instr := andI d 0x01010101
def rol1 (d : Reg) : Instr := rorI d 31

/-- The slices of the word in `eax`, in slots `0 … 7`. -/
def slices : List Instr :=
  st 0 .eax :: (List.range 7).flatMap fun j => [shrI .eax 1, st (j + 1) .eax]

/-- The S-box without its constant, from slots `0 … 7` to `subOut j`. -/
def subSlices : List Instr := [
  movS .eax 2, xorS .eax 5, movS .ebx 1, xorR .ebx .eax, movS .ecx 6, xorR .ecx .ebx, movS .edx 0,
  xorR .edx .ebx, movS .ebp 3, xorR .ebp .ecx, xorS .ebp 7, st 0 .ebx, movR .ebx .ebp, xorR .ebx .eax,
  st 2 .eax, movS .eax 4, xorR .eax .ebp, st 3 .eax, movR .eax .ebx, xorR .eax .edx, st 8 .ecx, movS .ecx 5,
  xorR .ecx .eax, st 5 .ecx, movS .ecx 4, xorR .ecx .eax, st 9 .ecx, movS .ecx 8, xorR .ecx .eax, st 10 .eax,
  movS .eax 5, xorS .eax 7, st 11 .edx, movS .edx 4, xorR .edx .ebx, xorS .ebp 9, st 4 .ebp, movS .ebp 5,
  xorR .ebp .edx, st 12 .ebp, movS .ebp 9, xorR .ebp .eax, st 13 .eax, movS .eax 1, xorR .eax .edx, st 1 .edx,
  movR .edx .ecx, xorR .edx .eax, st 14 .eax, movR .eax .ebp, andR .eax .ecx, st 15 .ecx, movS .ecx 12,
  andR .ecx .edx, st 16 .edx, movS .edx 1, andS .edx 4, st 17 .ebp, movS .ebp 7, xorS .ebp 11, xorR .eax .edx,
  xorR .ecx .eax, st 18 .ebp, movS .ebp 3, andS .ebp 11, xorR .ecx .ebp, xorR .ebx .ecx, movS .ecx 13,
  andS .ecx 8, st 19 .ebx, movS .ebx 7, andS .ebx 0, xorR .ecx .edx, movS .edx 10, andS .edx 9, xorR .ebp .ecx,
  xorR .ebx .edx, xorR .ecx .ebx, movS .ebx 14, andS .ebx 18, xorR .ebx .eax, xorR .edx .ebx, movS .eax 6,
  xorS .eax 13, movS .ebx 5, andS .ebx 6, xorS .edx 2, xorR .ebp .ebx, xorR .ecx .eax, movS .eax 5, xorS .eax 0,
  movR .ebx .ecx, andR .ebx .edx, xorR .eax .ebp, movS .ebp 19, xorR .ebp .edx, xorR .ecx .eax, st 2 .ecx,
  movS .ecx 19, xorR .ecx .ebx, xorR .ebx .eax, andR .ebp .ebx, xorS .ebp 19, xorR .edx .ebp, movR .ebx .ecx,
  xorR .ebx .ebp, andS .ebx 19, xorR .edx .ebx, xorR .ebx .ecx, andS .ecx 2, xorR .ecx .eax, andR .ebx .ecx,
  movR .eax .ebp, xorR .eax .edx, xorS .ebx 2, st 2 .ecx, movS .ecx 5, andR .ecx .eax, andS .eax 6, st 5 .eax,
  movS .eax 13, andR .eax .edx, st 6 .eax, movS .eax 15, andR .eax .ebx, st 13 .ecx, movR .ecx .ebx,
  xorR .ecx .edx, st 15 .eax, movS .eax 10, andR .eax .ecx, andS .edx 8, st 8 .eax, movS .eax 7, andR .eax .ebp,
  st 7 .eax, movS .eax 17, andR .eax .ebx, st 10 .eax, movS .eax 9, andR .eax .ecx, xorS .ebx 2, st 9 .eax,
  movS .eax 0, andR .eax .ebp, xorR .edx .eax, st 0 .edx, movS .edx 16, andR .edx .ebx, xorS .ebp 2,
  andS .ebx 12, st 12 .eax, movS .eax 3, andR .eax .ebp, xorS .edx 15, xorR .ecx .ebp, xorR .eax .edx,
  st 3 .eax, movS .eax 4, andR .eax .ecx, andS .ecx 1, xorR .edx .eax, xorS .ecx 10, andS .ebp 11,
  xorR .ebp .ebx, xorR .ebp .ecx, xorS .ecx 9, xorS .ebx 7, xorR .ebx .ecx, xorS .ebx 13, st 1 .ebx,
  movS .ebx 18, andS .ebx 2, xorR .ecx .ebx, xorS .edx 12, st 4 .ecx, movS .ecx 14, andS .ecx 2, xorS .eax 4,
  xorS .ecx 15, xorS .ecx 0, xorR .ebp .ecx, xorS .ecx 4, xorR .ebx .ebp, st 2 .ecx, movS .ecx 0,
  xorR .ecx .eax, xorS .ebx 6, xorS .eax 1, xorS .edx 5, xorS .eax 3, xorS .ebx 10, xorS .edx 8, xorS .ecx 8,
  xorS .ebx 7]

/-- The four bytes, without the constant, in `eax`. -/
def gather : List Instr := [
  bit0 .ecx, bit0 .eax, rol1 .ecx, xorR .ecx .eax, movS .eax 2, bit0 .eax, rol1 .ecx, xorR .ecx .eax, bit0 .ebx,
  rol1 .ecx, xorR .ecx .ebx, bit0 .edx, rol1 .ecx, xorR .ecx .edx, movS .edx 1, bit0 .edx, rol1 .ecx,
  xorR .ecx .edx, movS .edx 4, bit0 .edx, rol1 .ecx, xorR .ecx .edx, bit0 .ebp, rol1 .ecx, xorR .ecx .ebp,
  movR .eax .ecx]

def subWordCode : List Instr := slices ++ subSlices ++ gather ++ [.alu .xor .eax (.imm 0x63636363)]

/-! ## The words -/

def rcOff : Nat := 272
def jmOff : Nat := 276
def nkOff : Nat := 280
def leftOff : Nat := 284

/-- ROTWORD of `eax`, the round constant added, and the next round constant:
twice it in GF(2⁸), the reduction by a mask of its highest bit. -/
def rotTail : List Instr :=
  [rorI .eax 8, .alu .xor .eax (.mem (at_ .edi rcOff)), .mov .ebx (.mem (at_ .edi rcOff)), movR .ecx .ebx,
   shrI .ecx 7, movI .edx 0, subR .edx .ecx, andI .edx 0x1b, addR .ebx .ebx, xorR .ebx .edx, andI .ebx 0xff,
   .store (at_ .edi rcOff) .ebx]

def rotWordStep : List Instr := subWordCode ++ rotTail

/-- The word before, transformed by its place in the group of `Nk`, in `eax`. -/
def wordTemp : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .ecx (.mem (at_ .edi jmOff)), .alu .test .ecx (.reg .ecx)]

def wordTransform : Prog isa :=
  .ite .e (.block rotWordStep)
    (.seq (.block [.alu .cmp .ecx (.imm 16)])
      (.ite .e (.seq (.block [.mov .ecx (.mem (at_ .edi nkOff)), .alu .cmp .ecx (.imm 32)])
          (.ite .e (.block subWordCode) (.block [])))
        (.block [])))

/-- The new word, and the counters; ZF is set after the last word. The stores
of the schedule's words are through a pointer the constant-time analysis does
not follow, so the counters are stored again after each. -/
def wordStore : Prog isa :=
  .seq (.block [.mov .ecx (.mem (at_ .edi nkOff)), movR .ebx .esi, addI .ebx 4, subR .ebx .ecx,
      .alu .xor .eax (.mem (at_ .ebx 0)), .mov .ecx (.mem (at_ .edi jmOff)), .mov .edx (.mem (at_ .edi leftOff)),
      .mov .ebp (.mem (at_ .edi nkOff)), .store (at_ .esi 4) .eax, addI .esi 4, addI .ecx 4,
      .alu .cmp .ecx (.reg .ebp)])
    (.seq (.ite .e (.block [movI .ecx 0]) (.block []))
      (.block [.store (at_ .edi jmOff) .ecx, .store (at_ .edi nkOff) .ebp, subI .edx 1,
        .store (at_ .edi leftOff) .edx]))

def wordBody : Prog isa := .seq (.block wordTemp) (.seq wordTransform wordStore)

/-! ## The function -/

def copySetup : List Instr :=
  [.mov .esi (.mem (argOp 0)), .mov .ebp (.mem (argOp 2)), .mov .ecx (.mem (argOp 1))]

def copyBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, addI .esi 4, addI .ebp 4, subI .ecx 4]

/-- The last word of the key, and the counters: `3 Nk + 28` words are left. -/
def wordSetup : List Instr :=
  [movR .esi .ebp, subI .esi 4, movI .eax 0, .store (at_ .edi jmOff) .eax,
   .mov .eax (.mem (argOp 1)), .store (at_ .edi nkOff) .eax, shrI .eax 2, movR .ebx .eax, addR .eax .eax,
   addR .eax .ebx, addI .eax 28, .store (at_ .edi leftOff) .eax, movI .eax 1, .store (at_ .edi rcOff) .eax]

def expandKey : Prog isa :=
  .seq (.block (saveRegs 3 ++ copySetup)) (.seq (.loop (.block copyBody) .ne)
    (.seq (.block wordSetup) (.seq (.loop wordBody .ne) (.block restoreRegs))))

end VG.Impl.Aes.X86
