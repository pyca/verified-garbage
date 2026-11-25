module

public import VerifiedGarbage.Impl.Aes.X86_64.Linear
public import VerifiedGarbage.Impl.Seed.Layers

/-!
# SEED's G on sixteen words on x86-64

`g16` replaces each of the sixteen 32-bit words in the slots `tSlot 0 …
tSlot 7` of the scratch buffer (`r9`) with `G` of it, through AES's S-box on
bit planes (`Impl/Seed/Layers.lean`):

* `g16In` transposes the words into planes and applies `M` to them, XORing
  planes into others; those end in another order than the words began in,
  which the registers the words are loaded into (`inReg`) undo.
* AES's `sboxCode`, on slots 0–47.
* `g16Out` applies `P0` to the planes' even bytes and `P1` to their odd ones
  (`P0` to all, and `P0 ⊕ P1` to the odd ones, `dLin`), mixes the bytes of
  each 32-bit word, transposes back and adds `G`'s constant.

The mixing: output byte `a'` is the XOR of the word's four bytes `a`, each
without the pair of bits `(a + a') mod 4`. So bits `2b` and `2b + 1` of it
are those of the XOR of all four bytes (`spreadXor`), but for byte
`b - a' mod 4`, and `a' ↦ b - a' mod 4` exchanges bytes (`swaps`).
-/

@[expose] public section

namespace VG.Impl.Seed.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- The words, two in each slot. -/
def tSlot (i : Nat) : Nat := 61 + i

/-- The masks, by slot: the transpose's (48–50), the odd bytes (51), the
exchanges of bytes (52–55, the first also the lowest byte of each 32-bit
word) and `G`'s constant (56). -/
def maskSlots : List (Nat × BitVec 64) :=
  [(48, 0x5555555555555555), (49, 0x3333333333333333), (50, 0x0F0F0F0F0F0F0F0F), (51, 0xFF00FF00FF00FF00),
   (52, 0x000000FF000000FF), (53, 0x0000FF000000FF00), (54, 0x00FF00FF00FF00FF), (55, 0x0000FFFF0000FFFF),
   (56, gConst)]

def setG16Masks : List Instr := setMasks maskSlots

/-- The slots of the S-box's outputs, and of `dLin`'s. -/
def sSlot (j : Nat) : Nat := 8 + j
def dSlotG (j : Nat) : Nat := 16 + j

/-- Exchange index bit `i` of the bits with bit `i` of the number of the words in `r`. -/
def exch (r : Nat → Reg) (i : Nat) : List Instr :=
  ((List.range 8).filter fun k => k / 2 ^ i % 2 == 0).flatMap fun k =>
    swapMove (r k) (r (k + 2 ^ i)) t0 (48 + i) (2 ^ i)

/-- The transpose of the words in `r`. -/
def orthoR (r : Nat → Reg) : List Instr := exch r 2 ++ exch r 1 ++ exch r 0

/-- XOR registers into others. -/
def xors (r : Nat → Reg) (l : List (Nat × Nat)) : List Instr := l.map fun p => xorR (r p.1) (r p.2)

/-- Where word `k` goes, so that plane `i` of `M` is in `q i`. -/
def inReg : Nat → Reg
  | 0 => q 0 | 1 => q 3 | 2 => q 4 | 3 => q 6 | 4 => q 5 | 5 => q 7 | 6 => q 1 | _ => q 2

/-- `M`. -/
def mLin : List (Nat × Nat) :=
  [(5, 4), (7, 5), (0, 3), (0, 1), (1, 4), (4, 3), (3, 5), (5, 6), (6, 7), (3, 2), (6, 3), (2, 1), (1, 3)]

def g16In : List Instr :=
  ((List.range 8).map fun k => movS (inReg k) (tSlot k)) ++ orthoR inReg ++ xors inReg mLin

/-- `P0 ⊕ P1`, whose plane `i` ends in `q (dOut i)`. -/
def dLin : List (Nat × Nat) :=
  [(2, 1), (3, 2), (4, 0), (0, 6), (6, 7), (6, 1), (1, 4), (4, 5), (5, 2), (2, 7), (7, 3), (4, 3), (0, 4), (2, 1)]

def dOut : Nat → Nat
  | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 7 | 4 => 2 | 5 => 1 | 6 => 4 | _ => 6

/-- `P0`, whose plane `i` ends in `outReg i`. -/
def p0Lin : List (Nat × Nat) :=
  [(4, 6), (2, 4), (6, 3), (4, 0), (6, 1), (3, 2), (3, 0), (1, 4), (4, 5), (0, 5), (5, 2), (2, 7), (7, 6), (6, 0), (0, 2)]

def outReg : Nat → Reg
  | 0 => q 5 | 1 => q 2 | 2 => q 1 | 3 => q 0 | 4 => q 3 | 5 => q 6 | 6 => q 4 | _ => q 7

/-- In every byte of each 32-bit word of `t0`, the XOR of those of `r`. -/
def spreadXor (r : Reg) : List Instr :=
  [movR t0 r, shrI t0 16, xorR t0 r, movR t1 t0, shrI t1 8, xorR t0 t1, andS t0 52,
   movR t1 t0, rolI t1 8, xorR t0 t1, movR t1 t0, rolI t1 16, xorR t0 t1]

/-- Byte `a` and byte `b - a mod 4` of each 32-bit word of `r` exchanged. -/
def swaps (r : Reg) : Nat → List Instr
  | 0 => swapIn r t1 53 16
  | 1 => swapIn r t1 54 8
  | 2 => swapIn r t1 52 16
  | _ => swapIn r t1 54 8 ++ swapIn r t1 55 16

/-- The mixing of plane `j`, in `r`. -/
def mixPlane (r : Reg) (j : Nat) : List Instr := spreadXor r ++ swaps r (j / 2) ++ [xorR r t0]

def g16Out : List Instr :=
  ((List.range 8).map fun j => st (sSlot j) (q j)) ++ xors q dLin ++
  ((List.range 8).flatMap fun j => [andS (q (dOut j)) 51, st (dSlotG j) (q (dOut j))]) ++
  ((List.range 8).map fun j => movS (q j) (sSlot j)) ++ xors q p0Lin ++
  ((List.range 8).flatMap fun j => [xorS (outReg j) (dSlotG j)] ++ mixPlane (outReg j) j) ++
  orthoR outReg ++ (List.range 8).flatMap fun k => [xorS (outReg k) 56, st (tSlot k) (outReg k)]

/-- `G` of the sixteen words. -/
def g16 : List Instr := g16In ++ sboxCode ++ g16Out

end VG.Impl.Seed.X86_64
