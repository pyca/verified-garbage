module

public import VerifiedGarbage.Impl.X448.AArch64.Tail

/-!
# X448: AArch64 implementation

`vg_x448(out = x0, scalar = x1, point = x2, scratch = x3)`.

Field elements are sixteen normalized 28-bit limbs in 64-bit words.
Multiplication packs them into eight 56-bit limbs, accumulates two-word product
coefficients in registers, folding with
`2^448 = 2^224 + 1`. Squaring computes each cross product once. One wide
carry pass and two narrow passes restore normalized 28-bit slots. Pointwise
operations fuse coefficient arithmetic with their first carry pass. The ladder and
inversion addition chain follow the same arithmetic as the x86-64 baseline.

`x3` holds the working space, `x1` the output pointer after scalar decoding,
`x19` the ladder or squaring counter. Multiplication uses caller-saved
registers for its operands and coefficients.
`x20` saves the output pointer during setup. The two callee-saved registers
are saved in the working space and restored before returning. `x12` holds
`2^28 - 1` throughout. Only pointers and counters affect addresses or branches.
-/

@[expose] public section

namespace VG.Impl.X448.AArch64

open VG.AArch64

/-- Copy the sixteen limbs. -/
def copy (o a : Nat) : List Instr :=
  (List.range 16).flatMap fun i => [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]

/-- One carry step, with the incoming carry in `x6`. -/
def carryStep (o a i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), .add .x .x4 .x4 .x6,
    .logic .and .x .x5 .x4 .x12, st .x5 (o + 8 * i), .lsr .x .x6 .x4 28]

def pass (o a : Nat) : List Instr :=
  .movz .x .x6 0 0 :: (List.range 16).flatMap (carryStep o a)

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

/-- Decode seven bytes into two limbs without reading past the input. -/
def decodePair (i : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 7).flatMap (fun j =>
    [.lsl .x .x4 .x4 8, .ldrb .x7 .x2 (7 * i + (6 - j)), .add .x .x4 .x4 .x7]) ++
  [.logic .and .x .x7 .x4 .x12, st .x7 (X1 + 16 * i), st .x7 (X3 + 16 * i),
    .lsr .x .x4 .x4 28, st .x4 (X1 + 16 * i + 8), st .x4 (X3 + 16 * i + 8)]

/-- One scalar byte, expanded into eight bits. -/
def bitsBody : List Instr :=
  [.add .x .x11 .x1 .x19, .ldrb .x4 .x11 0,
    .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11] ++
  (List.range 8).flatMap (fun j =>
    [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (BITS + j)]) ++
  [.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 56]

/-- Expand the scalar and apply the RFC 7748 clamp. -/
def bits : Prog isa :=
  .seq (.block [.movz .x .x19 0 0, .movz .x .x8 1 0])
    (.seq (.loop (.block bitsBody) (.nonzero .x .x11))
      (.block [.movz .x .x4 0 0, .strb .x4 .x3 BITS, .strb .x4 .x3 (BITS + 1),
        .movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)]))

/-- Initialize all slots except the decoded coordinate. -/
def initSlots : List Instr :=
  [.movz .x .x4 0 0] ++
  (List.range 32).map (fun i => st .x4 (X2 + 8 * i)) ++
  (List.range 288).map (fun i => st .x4 (Z3 + 8 * i)) ++
  [st .x4 SWAP, .movz .x .x4 1 0, st .x4 X2, st .x4 Z3]

def setup : List Instr :=
  [st .x19 0, st .x20 8, .addImm .x .x20 .x0 0,
    .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
  (List.range 8).flatMap decodePair ++ initSlots

/-- Add `1 + 2^224`: its carry is one exactly when `[X2] >= p`. -/
def freeze : List Instr :=
  copy TMP X2 ++ [0, 8].flatMap (fun i =>
    [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1, st .x4 (TMP + 8 * i)]) ++ pass TMP TMP ++
  [.movz .x .x7 0 0, .sub .x .x7 .x7 .x6] ++
  (List.range 16).flatMap fun i =>
    [ld .x4 (X2 + 8 * i), ld .x5 (TMP + 8 * i), .logic .eor .x .x5 .x5 .x4,
      .logic .and .x .x5 .x5 .x7, .logic .eor .x .x4 .x4 .x5, st .x4 (X2 + 8 * i)]

/-- Pack two limbs into seven output bytes. -/
def packPair (i : Nat) : List Instr :=
  [ld .x4 (X2 + 16 * i + 8), .lsl .x .x4 .x4 28,
    ld .x5 (X2 + 16 * i), .add .x .x4 .x4 .x5] ++
  (List.range 7).flatMap fun j => [.strb .x4 .x1 (7 * i + j), .lsr .x .x4 .x4 8]

end VG.Impl.X448.AArch64
