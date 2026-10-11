module

public import VerifiedGarbage.Impl.Weierstrass.X86.Inv

/-! # Multiword helpers for the 32-bit divstep matrix updates -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86.Inv
open VG.X86 VG.Impl.Mont.X86

/-- Copy words through the mask in `ecx`. -/
def maskCopy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, dst, src =>
    [.mov .eax (.mem (sc src)), .alu .and .eax (.reg .ecx), .store (sc dst) .eax] ++
      maskCopy k (dst + 4) (src + 4)

/-- Subtract `src` from `dst`, modulo the width of the destination. -/
def subInPlace (dst src n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .eax (.mem (sc (dst + 4 * j))),
     .alu (if j = 0 then .sub else .sbb) .eax (.mem (sc (src + 4 * j))),
     .store (sc (dst + 4 * j)) .eax]

def addInPlace (dst src n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .eax (.mem (sc (dst + 4 * j))),
     .alu (if j = 0 then .add else .adc) .eax (.mem (sc (src + 4 * j))),
     .store (sc (dst + 4 * j)) .eax]

/-- Add an unsigned word times a multiword input to a wide accumulator. -/
def rowAdd (coefficient acc src n : Nat) : List Instr :=
  [.mov .ecx (.mem (sc coefficient)), .mov .ebp (.reg .edi)] ++ mulRow acc src n

def linearUnsigned (u v acc a b n : Nat) : List Instr :=
  zeros acc (n + 2) ++ rowAdd u acc a n ++ rowAdd v acc b n

/-- All ones in `ecx` exactly when a coefficient's signed value is negative. -/
def maskOf (coefficient : Nat) : List Instr :=
  [.mov .eax (.mem (sc coefficient)), .shift .shr .eax 31,
   .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax)]

/-- Correct an unsigned product for a negative coefficient, modulo `n`
words: subtract the masked input shifted by one word. -/
def correction (coefficient acc src tmp n : Nat) : List Instr :=
  maskOf coefficient ++ maskCopy (n - 1) tmp src ++ subInPlace (acc + 4) tmp (n - 1)

/-- A signed linear combination, retained modulo `k + 2` words. Inputs
have `n` words; the coefficients are signed 32-bit words. -/
def linear (u v acc a b tmp n k : Nat) : List Instr :=
  linearUnsigned u v acc a b n ++ correction u acc a tmp (k + 2) ++ correction v acc b tmp (k + 2)

/-- Store one word of a right shift by 30, from `eax` and `ebx`. -/
def shrTail (dst : Nat) : List Instr :=
  [.shift .shr .eax 30, .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx),
   .alu .add .eax (.reg .ebx), .store (sc dst) .eax]

def shrStep (dst src j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (src + 4 * j))), .mov .ebx (.mem (sc (src + 4 * (j + 1))))] ++
    shrTail (dst + 4 * j)

/-- Arithmetic right shift of a nonempty signed multiword value by 30. -/
def shr30 (dst src n : Nat) : List Instr :=
  (List.range (n - 1)).flatMap (shrStep dst src) ++ maskOf (src + 4 * (n - 1)) ++
    [.mov .eax (.mem (sc (src + 4 * (n - 1)))), .mov .ebx (.reg .ecx)] ++
    shrTail (dst + 4 * (n - 1))

/-- Add the modulus to a negative signed `n + 1`-word value. -/
def addIfNeg (acc modulus tmp n : Nat) : List Instr :=
  maskOf (acc + 4 * n) ++ maskCopy n tmp modulus ++ zeros (tmp + 4 * n) 1 ++
    addInPlace acc tmp (n + 1)

/-- Low word times the Montgomery constant, for a one-word reduction. -/
def quotientWord (src dst : Nat) (minv : BitVec 32) : List Instr :=
  [.mov .eax (.mem (sc src)), .mov .ecx (.imm minv), .mul .ecx, .store (sc dst) .eax]

/-- Add a saved sign-extension word after an unsigned product row. -/
def addSignWord (dst : Nat) : List Instr :=
  [.mov .eax (.mem (sc dst)), .alu .add .eax (.reg .esi), .store (sc dst) .eax]

/-- Form the sign-extended numerator of a one-word Montgomery reduction.
The sign word is added after the product row to keep that row unsigned. -/
def redSum (acc modulus tmp n : Nat) (minv : BitVec 32) : List Instr :=
  maskOf (acc + 4 * n) ++ [.mov .esi (.reg .ecx)] ++ zeros (acc + 4 * (n + 1)) 1 ++
    quotientWord acc tmp minv ++ rowAdd tmp acc modulus n ++ addSignWord (acc + 4 * (n + 1))

def reduce (M : VG.Impl.Mont.Mod) (acc tmp out : Nat) : List Instr :=
  redSum acc M.mo tmp (words M) (minv32 M) ++ addIfNeg (acc + 4) M.mo tmp (words M) ++
    csub M (acc + 4) out

end VG.Impl.Weierstrass.X86.Inv
