module

public import VerifiedGarbage.Impl.Sm4.X86.Sbox
public import VerifiedGarbage.Impl.Sm4.Lin
public import VerifiedGarbage.Impl.Aes.X86.Ctr32

/-!
# The layers of bitsliced SM4 on x86 (32-bit)

As on ARMv7 (`Impl/Sm4/Arm/Layers.lean`): eight blocks at a time, on
32-bit planes. Each of the four 32-bit words `X₀ … X₃` of the eight blocks
is eight planes: bit `8 i + b` of plane `j` of word `w` is bit `j` of byte
`i` (from the most significant) of word `w` of block `b`. So a rotation of
the words by 8 bits is a rotation of the planes by 8, and `L` and `L'` are,
on each plane, XORs of rotations of the planes by multiples of 8 bits.

Every plane lives in the scratch buffer at `edi`, in 4-byte slots: the
S-box's planes and spills (0–31), the planes of the state's four words
(32–63), the tail buffer (64–95, eight blocks), the table of the 32
bitsliced round keys, eight planes each, in the order the rounds use them
(96–351), the callee-saved registers `ebx`, `esi`, `edi` and `ebp`
(352–355), and the data pointer and the blocks left (or the schedule's
pointer) (356, 357). The round key's entry is at `kp` (`esi`).

Loading word `w` of the eight blocks (little-endian, so byte `i` from the
most significant is at bits `8 i … 8 i + 7`) into slots `0 … 7`, AES's
`ortho` (the 8×8 bit transpose in each byte position) gives its planes,
and back.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86 VG.Impl.Aes.X86
open VG.Impl.Sm4 (Lin)

/-- The round keys' pointer. -/
def kp : Reg := .esi

/-! ## Slots -/

/-- Plane `j` of the state's word `w`. -/
def stateSlot (w j : Nat) : Nat := 32 + 8 * w + j

/-- Word `w` of block `b` of the tail buffer. -/
def tailSlot : Nat := 64
def tailAt (b w : Nat) : Nat := tailSlot + 4 * b + w

/-- The table of round keys, and its end. -/
def tableSlot : Nat := 96
def tableEnd : Nat := tableSlot + 8 * 32

def savedSlot : Nat := tableEnd
def dSlot : Nat := savedSlot + 4
def nSlot : Nat := dSlot + 1

/-- The number of slots, rounded up to a whole number of 64-bit words (the
artifacts allocate the buffer as `[u64; 179]`). -/
def slots : Nat := nSlot + 1

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.ebx, savedSlot), (.esi, savedSlot + 1), (.edi, savedSlot + 2), (.ebp, savedSlot + 3)]

/-- Load the scratch buffer's address (argument `k`) to `edi`, saving the
registers there first. -/
def saveRegs (k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp k))] ++ savedRegs.map (fun (r, j) => .store (slotAt .eax j) r) ++ [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def restoreRegs : List Instr :=
  [movS .ebx savedSlot, movS .esi (savedSlot + 1), movS .ebp (savedSlot + 3), movS .edi (savedSlot + 2)]

/-! ## Between blocks and planes -/

/-- Word `w` of the eight blocks of the tail buffer to the planes of the
state's word `w`. -/
def toBsWord (w : Nat) : List Instr :=
  (List.range 8).flatMap (fun b => [movS .eax (tailAt b w), st b .eax]) ++ ortho ++
  (List.range 8).flatMap (fun j => [movS .eax j, st (stateSlot w j) .eax])

/-- The eight blocks of the tail buffer to the planes of the state's words. -/
def toBs : List Instr := (List.range 4).flatMap toBsWord

/-- The planes of the state's word `3 - w` to word `w` of the eight blocks
(SM4's final reversal `R`); the state is kept. -/
def fromBsWord (w : Nat) : List Instr :=
  (List.range 8).flatMap (fun j => [movS .eax (stateSlot (3 - w) j), st j .eax]) ++ ortho ++
  (List.range 8).flatMap (fun b => [movS .eax b, st (tailAt b w) .eax])

/-- The planes back to the eight blocks in the tail buffer. -/
def fromBs : List Instr := (List.range 4).flatMap fromBsWord

/-! ## A round -/

/-- The S-box's input, `X_b ⊕ X_c ⊕ X_d ⊕ rk`, with the round key at
entry `e` of `kp`. -/
def preX (e b c d : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    [movS .eax (stateSlot b j), xorS .eax (stateSlot c j), xorS .eax (stateSlot d j),
     .alu .xor .eax (.mem (slotAt kp (8 * e + j))), st j .eax]

/-- Plane `j` of `L(B)`, with `B`'s planes in slots `0 … 7`, XORed into the
state's word `a`: with `Qⱼ` the planes of `B ⋘ 2` (`Bⱼ₋₂`, or `Bⱼ₊₆`
rotated a byte), `Bⱼ ⊕ (Bⱼ ⋘ 24) ⊕ Qⱼ ⊕ (Qⱼ ⋘ 8) ⊕ (Qⱼ ⋘ 16)`. -/
def linStep (a j : Nat) : List Instr :=
  (if 2 ≤ j then [movS .eax (j - 2)] else [movS .eax (j + 6), rorI .eax 8]) ++
  [movR .ebx .eax, rorI .ebx 8, xorR .ebx .eax, movR .ecx .eax, rorI .ecx 16, xorR .ebx .ecx,
   movS .eax j, xorR .ebx .eax, rorI .eax 24, xorR .ebx .eax,
   xorS .ebx (stateSlot a j), st (stateSlot a j) .ebx]

/-- `X_a ⊕= L(B)`. -/
def linL (a : Nat) : List Instr := (List.range 8).flatMap (linStep a)

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)` XORed into the state's
word `a`. -/
def keyLinStep (a j : Nat) : List Instr :=
  [movS .ebx j] ++
  (if 5 ≤ j then [movS .eax (j - 5), rorI .eax 8] else [movS .eax (j + 3), rorI .eax 16]) ++
  [xorR .ebx .eax] ++
  (if j = 7 then [movS .eax 0, rorI .eax 16] else [movS .eax (j + 1), rorI .eax 24]) ++
  [xorR .ebx .eax, xorS .ebx (stateSlot a j), st (stateSlot a j) .ebx]

/-- `X_a ⊕= L'(B)`. -/
def linK (a : Nat) : List Instr := (List.range 8).flatMap (keyLinStep a)

def lin : Lin → Nat → List Instr
  | .enc => linL
  | .key => linK

/-- A round: `X_a ⊕= T(X_b ⊕ X_c ⊕ X_d ⊕ rk)`, the round key at entry `e` of `kp`. -/
def round (l : Lin) (e a b c d : Nat) : List Instr := preX e b c d ++ sboxCode ++ lin l a

/-- Four rounds, whose new words replace `X₀ … X₃` in turn. -/
def rounds4 (l : Lin) : List Instr :=
  round l 0 0 1 2 3 ++ round l 1 1 2 3 0 ++ round l 2 2 3 0 1 ++ round l 3 3 0 1 2

/-! ## The round keys' planes -/

/-- The round key at `ecx`, its bytes reversed (the word's bytes are
little-endian, the state's from the most significant), to slot 0. -/
def keyWord : List Instr := [.mov .eax (.mem (at_ .ecx 0)), .bswap .eax, st 0 .eax]

/-- Plane `j` of the round key, to word `j` of the entry at `kp`: bit `j` of
each byte of slot 0, masked into `ebx` and spread over its byte by three
shifted XORs (their bits never overlap), through `edx`. -/
def keyPlane (j : Nat) : List Instr :=
  [movS .ebx 0] ++ (if j = 0 then [] else [shrI .ebx j]) ++
  [andI .ebx 0x01010101, movR .edx .ebx, rorI .edx 31, xorR .ebx .edx, movR .edx .ebx, rorI .edx 30,
   xorR .ebx .edx, movR .edx .ebx, rorI .edx 28, xorR .ebx .edx, .store (slotAt kp j) .ebx]

/-- The round key's planes to the entry at `kp`, through `ebx` and `edx`. -/
def keyPlanes : List Instr := (List.range 8).flatMap keyPlane

def keyOne : List Instr := keyWord ++ keyPlanes

end VG.Impl.Sm4.X86
