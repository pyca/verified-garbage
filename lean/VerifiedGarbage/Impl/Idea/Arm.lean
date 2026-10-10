import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Idea.Key32

/-!
# IDEA on ARMv7

The same algorithms as on AArch64 (`Impl/Idea/AArch64.lean`), on 32-bit
registers: `r12` holds the mask `0xffff`, and `r8`, `r9` are ⊙'s working
registers.

## ⊙ without branches

`mulCode d a b` computes `d := a ⊙ b` on the low 16 bits of `a` and `b`.
Each operand becomes its residue `((x - 1) & 0xffff) + 1` (0 stands for
2¹⁶), and `mul` (the model's only multiplication, whose timing does not
depend on its operands; see `TCB/Arm/Isa.lean`) gives the low 32 bits of
their product `p ≤ 2³²`, of which the code keeps `q = p - 1 < 2³²`, which no
wrap-around changes. Since `2¹⁶ ≡ -1`, `p = 2¹⁶ q_hi + q_lo + 1 ≡ q_lo + 1 -
q_hi` modulo 2¹⁶ + 1 (`q_lo = q & 0xffff`, `q_hi = q >> 16`); the difference
is in `-2¹⁶ + 2 … 2¹⁶`, and adding its sign bit, then keeping the low 16
bits, adds 2¹⁶ + 1 to a negative one: no branch, no division.

## `vg_idea_expand_key` (`key = r0`, `schedule = r1`)

Each 32-bit word of the schedule (two subkeys) is a fixed bit permutation of
the key's four 32-bit words (`expandWord w`: a group of bits with the same
rotation at a time, `ldr`, a mask built by `movw`/`movt`, `and` with the
word rotated, `eor`), assembled in `r12` and stored. Only `r2`, `r3` and
`r12` are written.

## `vg_idea_invert_key` (`schedule = r0`, `inverse = r1`, scratch `r2`)

Each decryption subkey is a copy, the negation or the ⊙-inverse of an
encryption subkey (`Impl.Idea.invOp`), the inverse `a ^ (2¹⁶ - 1)` by
fifteen iterations of `t := (t ⊙ t) ⊙ a`, a loop with a public count
(`a = r4`, `t = r5`, the count in `r6`). Two subkeys are assembled in `r7`
and stored. `r4`–`r9` are saved in the scratch buffer and restored.

## `vg_idea_ecb` (`schedule = r0`, `data = r1`, `n = r2`, scratch `r3`)

`cryptBlock` replaces the block at `r1` by its encryption under the subkeys
at `r0`, writing only `r4`–`r12`: the block is loaded into `r4`–`r7` (one
16-bit word each, a byte at a time), run through the eight rounds
(unrolled) and the output transformation, and stored a byte at a time.
Round `j` keeps `X₂` and `X₃` in `r5` and `r6` when `j` is even and in `r6`
and `r5` when it is odd, so the exchange of the middle words costs no
instruction; `t₀` and `t₁` are in `r10` and `r11`. Each subkey is read when
it is used, with a 32-bit load at its own offset, of which the code uses the
low 16 bits (the last, with a load at 100 shifted). `r2` counts the blocks
left, and `r4`–`r11` are saved in the scratch buffer and restored.

The only branches are on `n` and the loop counts.
-/

namespace VG.Impl.Idea.Arm

open VG.Arm VG.Impl.Idea

/-! ## ⊙ -/

/-- `d := a ⊙ b` (low 16 bits of each; the result zero-extended), through
`r8` and `r9`, with the mask `0xffff` in `r12`. `b` may be `r9`, not `r8`. -/
def mulCode (d a b : Reg) : List Instr := [
  .dp .sub .r8 a (.imm 1), .dp .and .r8 .r8 (.reg .r12), .dp .add .r8 .r8 (.imm 1),
  .dp .sub .r9 b (.imm 1), .dp .and .r9 .r9 (.reg .r12), .dp .add .r9 .r9 (.imm 1),
  .mul .r8 .r8 .r9,
  .dp .sub .r8 .r8 (.imm 1),
  .dp .and .r9 .r8 (.reg .r12), .dp .add .r9 .r9 (.imm 1),
  .dp .sub .r9 .r9 (.shifted .r8 .lsr 16),
  .dp .add .r9 .r9 (.shifted .r9 .lsr 31),
  .dp .and d .r9 (.reg .r12)]

/-- `r12 := 0xffff`. -/
def setMask : Instr := .movw .r12 0xffff

/-- Subkey `k` into the low 16 bits of `r`: a 32-bit load at its offset (for
the last, at 100, shifted). -/
def loadKey (r : Reg) (k : Nat) : List Instr :=
  if k = 51 then [.ldr r .r0 100, .mov r (.shifted r .lsr 16)] else [.ldr r .r0 (2 * k)]

/-! ## Key expansion -/

/-- The mask of a group into `r3`. -/
def movMask (c : Nat) : List Instr :=
  .movw .r3 (BitVec.ofNat 16 c) ::
    if c / 2 ^ 16 = 0 then [] else [.movt .r3 (BitVec.ofNat 16 (c / 2 ^ 16))]

/-- One group, its key word into `r2`, masked into `r12` (the first) or into
`r2` and then XORed into `r12`. -/
def groupCode (first : Bool) (g : Nat × Nat × Nat) : List Instr :=
  ([.ldr .r2 .r0 (4 * g.1)] : List Instr) ++ movMask g.2.2 ++
  [.dp .and (if first then .r12 else .r2) .r3
    (if g.2.1 = 0 then .reg .r2 else .shifted .r2 .ror g.2.1)] ++
  (if first then [] else [.dp .eor .r12 .r12 (.reg .r2)])

/-- Schedule word `w` into `r12`. -/
def expandWord (w : Nat) : List Instr :=
  (expandGroups32 w).zipIdx.flatMap fun (g, k) => groupCode (k = 0) g

def expandKey : Prog isa :=
  .block ((List.range 26).flatMap fun w => expandWord w ++ ([.str .r12 .r1 (4 * w)] : List Instr))

/-! ## Saving registers -/

/-- The registers `invertKey` saves, at their offsets in the scratch buffer. -/
def invSaved : List (Reg × Nat) := [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20)]

/-- The registers `ecb` saves, at their offsets in the scratch buffer. -/
def ecbSaved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28)]

def save (b : Reg) (l : List (Reg × Nat)) : List Instr := l.map fun p => .str p.1 b p.2

def restore (b : Reg) (l : List (Reg × Nat)) : List Instr := l.map fun p => .ldr p.1 b p.2

/-! ## Inversion -/

/-- `t := (t ⊙ t) ⊙ a` with `t = r5`, `a = r4`, and the count in `r6`. -/
def invStep : List Instr :=
  mulCode .r5 .r5 .r5 ++ mulCode .r5 .r5 .r4 ++ ([.subs .r6 .r6 (.imm 1)] : List Instr)

/-- Decryption subkey `n` into `r3`, zero-extended. -/
def invWord (n : Nat) : Prog isa :=
  match invOp n with
  | (.copy, k) => .block (loadKey .r3 k ++ ([.dp .and .r3 .r3 (.reg .r12)] : List Instr))
  | (.neg, k) => .block (loadKey .r3 k ++
      ([.mov .r9 (.imm 0), .dp .sub .r3 .r9 (.reg .r3), .dp .and .r3 .r3 (.reg .r12)] : List Instr))
  | (.inv, k) => .seq (.block (loadKey .r4 k ++ ([.mov .r5 (.reg .r4), .mov .r6 (.imm 15)] : List Instr)))
      (.seq (.loop (.block invStep) .ne) (.block [.mov .r3 (.reg .r5)]))

/-- Decryption subkey `n` into its place in `r7`. -/
def invPlace (n : Nat) : List Instr :=
  if n % 2 = 0 then [.mov .r7 (.reg .r3)] else [.dp .orr .r7 .r7 (.shifted .r3 .lsl 16)]

/-- Decryption subkeys `2q` and `2q + 1`, stored. -/
def invPair (q : Nat) : Prog isa :=
  (List.range 2).foldr (fun i rest => .seq (invWord (2 * q + i)) (.seq (.block (invPlace (2 * q + i))) rest))
    (.block [.str .r7 .r1 (4 * q)])

def invertKey : Prog isa :=
  .seq (.block (save .r2 invSaved ++ [setMask]))
    (.seq ((List.range 26).foldr (fun q rest => .seq (invPair q) rest) (.block []))
      (.block (restore .r2 invSaved)))

/-! ## A block -/

/-- The registers of `X₂` and `X₃` in round `j`. -/
def regB (j : Nat) : Reg := if j % 2 = 0 then .r5 else .r6

def regC (j : Nat) : Reg := if j % 2 = 0 then .r6 else .r5

/-- `r := (r + r9) & 0xffff`. -/
def addKey (r : Reg) : List Instr := [.dp .add r r (.reg .r9), .dp .and r r (.reg .r12)]

/-- Round `j` (0–7), with `X₁ … X₄` in `r4`, `b`, `c`, `r7`; after it, the
new `X₂` is in `c` and the new `X₃` in `b`. -/
def roundWith (j : Nat) (b c : Reg) : List Instr :=
  let o := 6 * j
  loadKey .r9 o ++ mulCode .r4 .r4 .r9 ++
  loadKey .r9 (o + 3) ++ mulCode .r7 .r7 .r9 ++
  loadKey .r9 (o + 1) ++ addKey b ++
  loadKey .r9 (o + 2) ++ addKey c ++
  ([.dp .eor .r10 .r4 (.reg c)] : List Instr) ++ loadKey .r9 (o + 4) ++ mulCode .r10 .r10 .r9 ++
  ([.dp .eor .r11 b (.reg .r7), .dp .add .r11 .r11 (.reg .r10)] : List Instr) ++
  loadKey .r9 (o + 5) ++ mulCode .r11 .r11 .r9 ++
  ([.dp .add .r10 .r10 (.reg .r11), .dp .and .r10 .r10 (.reg .r12),
    .dp .eor .r4 .r4 (.reg .r11), .dp .eor c c (.reg .r11),
    .dp .eor b b (.reg .r10), .dp .eor .r7 .r7 (.reg .r10)] : List Instr)

def round (j : Nat) : List Instr := roundWith j (regB j) (regC j)

/-- Word `k` of the block at `r1` into `r`, big-endian (through `r8`). -/
def loadWord (r : Reg) (k : Nat) : List Instr :=
  [.ldrb r .r1 (2 * k), .ldrb .r8 .r1 (2 * k + 1), .dp .orr r .r8 (.shifted r .lsl 8)]

/-- The block at `r1` into `r4`–`r7`, one big-endian word each. -/
def load : List Instr :=
  loadWord .r4 0 ++ loadWord .r5 1 ++ loadWord .r6 2 ++ loadWord .r7 3

/-- The output transformation (subkeys 48–51), after the eighth round (`X₂`
in `r5`, `X₃` in `r6`), with the middle words exchanged back: `r6` gets
`Y₂ = X₃ ⊞ Z₅₀`, `r5` gets `Y₃ = X₂ ⊞ Z₅₁`. -/
def output : List Instr :=
  loadKey .r9 48 ++ mulCode .r4 .r4 .r9 ++
  loadKey .r9 51 ++ mulCode .r7 .r7 .r9 ++
  loadKey .r9 49 ++ addKey .r6 ++
  loadKey .r9 50 ++ addKey .r5

/-- The word in `r` to word `k` of the block at `r1`, big-endian (through `r8`). -/
def storeWord (r : Reg) (k : Nat) : List Instr :=
  [.strb r .r1 (2 * k + 1), .mov .r8 (.shifted r .lsr 8), .strb .r8 .r1 (2 * k)]

/-- `r4, r6, r5, r7` (`Y₁ … Y₄`) to the block at `r1`. -/
def store : List Instr :=
  storeWord .r4 0 ++ storeWord .r6 1 ++ storeWord .r5 2 ++ storeWord .r7 3

/-- The block at `r1`, under the subkeys at `r0`. -/
def cryptBlock : List Instr :=
  setMask :: (load ++ (List.range 8).flatMap round ++ output ++ store)

/-! ## ECB -/

def ecb : Prog isa :=
  .seq (.block (save .r3 ecbSaved ++ [.cmp .r2 (.imm 0)]))
    (.seq (.ite .eq (.block [])
        (.loop (.block (cryptBlock ++ ([.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] : List Instr)))
          .ne))
      (.block (restore .r3 ecbSaved)))

end VG.Impl.Idea.Arm
