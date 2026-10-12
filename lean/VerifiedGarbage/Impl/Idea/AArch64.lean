module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.Idea.Key

/-!
# IDEA on AArch64

The same algorithms as on x86-64 (`Impl/Idea/X86_64.lean`), in the
caller-saved registers `x0`–`x15`, with no stack: `x15` holds the mask
`0xffff`, and `x11`, `x12` are ⊙'s working registers.

## ⊙ without branches

`mulCode d a b` computes `d := a ⊙ b` on the low 16 bits of `a` and `b`:
each operand becomes its residue `((x - 1) & 0xffff) + 1` (0 stands for
2¹⁶), `mul` (whose timing does not depend on its operands) gives the product
`p ≤ 2³²`, and since `2¹⁶ ≡ -1`, `p ≡ lo - hi` modulo 2¹⁶ + 1 for
`lo = p & 0xffff`, `hi = p >> 16`, which the code corrects to `0 … 2¹⁶` by
adding `2¹⁶ + 1` times the sign bit of the 64-bit difference.

## `vg_idea_expand_key` (`key = x0`, `schedule = x1`)

Each quadword of the schedule is a fixed bit permutation of the key's two
quadwords (`expandWord q`: a group of bits with the same rotation at a
time, `ldr`, `ror`, `and` with a mask built by `movz`/`movk`, `eor`), stored
with `str`.

## `vg_idea_invert_key` (`schedule = x0`, `inverse = x1`)

Each decryption subkey is a copy, the negation or the ⊙-inverse of an
encryption subkey (`Impl.Idea.invOp`),
the inverse `a ^ (2¹⁶ - 1)` by fifteen iterations of `t := (t ⊙ t) ⊙ a`,
a loop with a public count. Four subkeys are assembled in `x9` and stored.

## `vg_idea_ecb` (`schedule = x0`, `data = x1`, `n = x2`)

Each block is loaded into `x3`–`x6` (one 16-bit word each, a byte at a
time), run through the eight rounds (unrolled) and the output
transformation, and stored a byte at a time; `x2` counts the blocks left.
A round's subkeys are loaded two at a time by 32-bit loads.

The only branches are on `n` and the loop counts.
-/

@[expose] public section

namespace VG.Impl.Idea.AArch64

open VG.AArch64 VG.Impl.Idea

/-! ## ⊙ -/

/-- `d := a ⊙ b` (low 16 bits of each; the result zero-extended), through
`x11` and `x12`, with the mask `0xffff` in `x15`. -/
def mulCode (d a b : Reg) : List Instr := [
  .subImm .x .x11 a 1, .logic .and .x .x11 .x11 .x15, .addImm .x .x11 .x11 1,
  .subImm .x .x12 b 1, .logic .and .x .x12 .x12 .x15, .addImm .x .x12 .x12 1,
  .mul .x .x11 .x11 .x12,
  .logic .and .x .x12 .x11 .x15, .lsr .x .x11 .x11 16,
  .sub .x .x12 .x12 .x11,
  .lsr .x .x11 .x12 63,
  .add .x .x12 .x12 .x11, .lsl .x .x11 .x11 16, .add .x .x12 .x12 .x11,
  .logic .and .x d .x12 .x15]

/-- `x15 := 0xffff`. -/
def setMask : Instr := .movz .x .x15 0xffff 0

/-! ## Key expansion -/

/-- The 64-bit constant `c` into `x10`. -/
def movConst (c : Nat) : List Instr :=
  .movz .x .x10 (BitVec.ofNat 16 c) 0 ::
    ([1, 2, 3].filter fun h => (c >>> (16 * h)) % 2 ^ 16 ≠ 0).map fun h =>
      .movk .x .x10 (BitVec.ofNat 16 (c >>> (16 * h))) h

/-- One group into `x9`, masked, then into `x11` (the first by `and`). -/
def groupCode (first : Bool) (g : Nat × Nat × Nat) : List Instr :=
  ([.ldr .x .x9 .x0 (8 * g.1)] : List Instr) ++
  (if g.2.1 = 0 then [] else [.ror .x .x9 .x9 g.2.1]) ++
  movConst g.2.2 ++
  [if first then .logic .and .x .x11 .x9 .x10 else .logic .and .x .x9 .x9 .x10] ++
  (if first then [] else [.logic .eor .x .x11 .x11 .x9])

/-- Schedule quadword `q` into `x11`. -/
def expandWord (q : Nat) : List Instr :=
  (expandGroups q).zipIdx.flatMap fun (g, k) => groupCode (k = 0) g

def expandKey : Prog isa :=
  .block ((List.range 13).flatMap fun q => expandWord q ++ ([.str .x .x11 .x1 (8 * q)] : List Instr))

/-! ## Inversion -/

/-- Encryption subkey `k` into the low 16 bits of `r`: a 32-bit load of the
pair it is in, shifted for the second of the pair (above them, for the first,
the second). -/
def loadKey (r : Reg) (k : Nat) : List Instr :=
  .ldr .w r .x0 (4 * (k / 2)) :: if k % 2 = 0 then [] else [.lsr .x r r 16]

/-- `t := (t ⊙ t) ⊙ a` with `t = x6`, `a = x5`, and the count in `x7`. -/
def invStep : List Instr :=
  mulCode .x6 .x6 .x6 ++ mulCode .x6 .x6 .x5 ++ ([.subImm .x .x7 .x7 1] : List Instr)

/-- Decryption subkey `n` into `x3`, zero-extended. -/
def invWord (n : Nat) : Prog isa :=
  match invOp n with
  | (.copy, k) => .block (loadKey .x3 k ++ ([.logic .and .x .x3 .x3 .x15] : List Instr))
  | (.neg, k) => .block (loadKey .x4 k ++
      ([.movz .x .x3 0 0, .sub .x .x3 .x3 .x4, .logic .and .x .x3 .x3 .x15] : List Instr))
  | (.inv, k) => .seq (.block (loadKey .x5 k ++ ([.addImm .x .x6 .x5 0, .movz .x .x7 15 0] : List Instr)))
      (.seq (.loop (.block invStep) (.nonzero .x .x7)) (.block [.addImm .x .x3 .x6 0]))

/-- Decryption subkey `n` into its place in `x9`. -/
def invPlace (n : Nat) : List Instr :=
  if n % 4 = 0 then [.addImm .x .x9 .x3 0]
  else [.lsl .x .x3 .x3 (16 * (n % 4)), .logic .orr .x .x9 .x9 .x3]

/-- Decryption subkeys `4q … 4q + 3`, stored. -/
def invQuad (q : Nat) : Prog isa :=
  (List.range 4).foldr (fun i rest => .seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest))
    (.block [.str .x .x9 .x1 (8 * q)])

def invertKey : Prog isa :=
  .seq (.block [setMask]) ((List.range 13).foldr (fun q rest => .seq (invQuad q) rest) (.block []))

/-! ## ECB -/

/-- `r := (r + k) & 0xffff`. -/
def addKey (r k : Reg) : List Instr := [.add .x r r k, .logic .and .x r r .x15]

/-- Round `j` (0–7), its subkeys at `x0 + 12 j`, on `x3`–`x6`. -/
def round (j : Nat) : List Instr :=
  let o := 12 * j
  ([.ldr .w .x8 .x0 o, .ldr .w .x9 .x0 (o + 4), .ldr .w .x13 .x0 (o + 8)] : List Instr) ++
  mulCode .x3 .x3 .x8 ++
  ([.lsr .x .x14 .x9 16] : List Instr) ++ mulCode .x6 .x6 .x14 ++
  ([.lsr .x .x14 .x8 16] : List Instr) ++ addKey .x4 .x14 ++
  addKey .x5 .x9 ++
  ([.logic .eor .x .x7 .x3 .x5] : List Instr) ++ mulCode .x7 .x7 .x13 ++
  ([.logic .eor .x .x14 .x4 .x6, .add .x .x14 .x14 .x7, .lsr .x .x10 .x13 16] : List Instr) ++
  mulCode .x14 .x14 .x10 ++
  ([.add .x .x7 .x7 .x14, .logic .and .x .x7 .x7 .x15,
   .logic .eor .x .x3 .x3 .x14, .logic .eor .x .x5 .x5 .x14,
   .logic .eor .x .x4 .x4 .x7, .logic .eor .x .x6 .x6 .x7,
   .addImm .x .x14 .x4 0, .addImm .x .x4 .x5 0, .addImm .x .x5 .x14 0] : List Instr)

/-- Word `k` of the block at `x1` into `r`, big-endian (through `x7`). -/
def loadWord (r : Reg) (k : Nat) : List Instr :=
  [.ldrb r .x1 (2 * k), .lsl .x r r 8, .ldrb .x7 .x1 (2 * k + 1), .logic .orr .x r r .x7]

/-- The block at `x1` into `x3`–`x6`, one big-endian word each. -/
def load : List Instr :=
  loadWord .x3 0 ++ loadWord .x4 1 ++ loadWord .x5 2 ++ loadWord .x6 3

/-- The output transformation (subkeys 48–51 in the quadword at 96), with
the middle words exchanged back: `x5` gets `X₃ ⊞ Z₅₀`, `x4` `X₂ ⊞ Z₅₁`. -/
def output : List Instr :=
  ([.ldr .x .x8 .x0 96] : List Instr) ++ mulCode .x3 .x3 .x8 ++
  ([.lsr .x .x14 .x8 48] : List Instr) ++ mulCode .x6 .x6 .x14 ++
  ([.lsr .x .x14 .x8 16] : List Instr) ++ addKey .x5 .x14 ++
  ([.lsr .x .x14 .x8 32] : List Instr) ++ addKey .x4 .x14

/-- The word in `r` to word `k` of the block at `x1`, big-endian (through `x14`). -/
def storeWord (r : Reg) (k : Nat) : List Instr :=
  [.strb r .x1 (2 * k + 1), .lsr .x .x14 r 8, .strb .x14 .x1 (2 * k)]

/-- `x3, x5, x4, x6` (Y₁ … Y₄) to the block at `x1`. -/
def store : List Instr :=
  storeWord .x3 0 ++ storeWord .x5 1 ++ storeWord .x4 2 ++ storeWord .x6 3

def cryptBlock : List Instr :=
  load ++ (List.range 8).flatMap round ++ output ++ store

def ecb : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block [setMask])
      (.loop (.block (cryptBlock ++ ([.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] : List Instr))) (.nonzero .x .x2)))

end VG.Impl.Idea.AArch64
