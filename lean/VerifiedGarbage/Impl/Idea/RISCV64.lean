module

public import VerifiedGarbage.Impl.Idea.Key
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# IDEA on RISC-V

The algorithm of the PPC64LE implementation (`Impl/Idea/PPC64LE.lean`) but
for the key schedule, with `t2` holding the mask `0xffff` and `t0`, `t1`
⊙'s working registers. The model faults on misaligned accesses and the
contracts state no alignment for the key, the schedules or the data, so all
of them are read and written a byte at a time.

## ⊙ without branches

`mulCode` computes `t1 := t0 ⊙ t1` on the low 16 bits of each, using only
`t0` and `t1`: each operand `x` becomes `((x - 1) & 0xffff) + 1`, its
residue in `1 … 2¹⁶` (0 stands for 2¹⁶); `mul` (whose timing does not
depend on its operands; see `TCB/RISCV64/Isa.lean`) gives the product
`p ≤ 2³²`; and since `2¹⁶ ≡ -1`, `p ≡ lo - hi` modulo 2¹⁶ + 1 for
`lo = p & 0xffff`, `hi = p >> 16`, which the code corrects to `0 … 2¹⁶` by
adding `2¹⁶ + 1` times the sign bit of the 64-bit difference: no branch,
no division.

## `vg_idea_expand_key` (`key = a0`, `schedule = a1`)

The key, as a 128-bit big-endian number (`Spec.Idea.keyValue`), is loaded
into `a2` (its high half) and `a3` (`loadBE64`). Subkey `8j + i` is the
16-bit window at bit `16 (7 - i)` of the key rotated left by `25 j` bits,
which lies in one of the two halves: it is shifted down into `t0` and
stored, low byte first. Between groups of eight subkeys the pair is rotated
left by 25 bits (`rotate`, through `t0` and `t1`).

## `vg_idea_invert_key` (`schedule = a0`, `inverse = a1`)

Each decryption subkey is a copy, the negation or the ⊙-inverse of an
encryption subkey (`invOp`), computed in `t1` and stored. The inverse of
`a` (`a3`) is `a ^ (2¹⁶ - 1)`: fifteen iterations of `t := (t ⊙ t) ⊙ a`
from `t = a` (`a4`), a loop with a public count (`a2`).

## `vg_idea_ecb` (`schedule = a0`, `data = a1`, `n = a2`)

Each block is loaded into `a3`–`a6` (one 16-bit word each, a byte at a
time), run through the eight rounds (unrolled) and the output
transformation, and stored; `a7` holds a round's `t₀`, and `a2` counts the
blocks left. A subkey is read with two byte loads (`loadKey`, through `t3`).

Only temporaries and argument registers are used, and no stack. The only
branches are on `n` and the loop counts.
-/

@[expose] public section

namespace VG.Impl.Idea.RISCV64

open VG.RISCV64 VG.Impl.Idea

/-- `d := s` (`addi d, s, 0`). -/
def mov (d s : Reg) : Instr := .addi d s 0

/-! ## ⊙ -/

/-- `t1 := t0 ⊙ t1` (low 16 bits of each; the result zero-extended),
clobbering `t0`, with the mask `0xffff` in `t2`. -/
def mulCode : List Instr := [
  .addi .t0 .t0 (-1), .logic .and .t0 .t0 .t2, .addi .t0 .t0 1,
  .addi .t1 .t1 (-1), .logic .and .t1 .t1 .t2, .addi .t1 .t1 1,
  .mul .t0 .t0 .t1,
  .logic .and .t1 .t0 .t2, .shift .srl .d .t0 .t0 16,
  .sub .t1 .t1 .t0,
  .shift .srl .d .t0 .t1 63,
  .add .t1 .t1 .t0, .shift .sll .d .t0 .t0 16, .add .t1 .t1 .t0,
  .logic .and .t1 .t1 .t2]

/-- `t2 := 0xffff` (`lui` of `0x10000`, less one). -/
def setMask : List Instr := [.lui .t2 16, .addi .t2 .t2 (-1)]

/-- Subkey `k` of the schedule at `a0` into `r`, zero-extended: its two
bytes, little-endian (through `t3`). -/
def loadKey (r : Reg) (k : Nat) : List Instr :=
  [.load .b r .a0 (2 * k), .load .b .t3 .a0 (2 * k + 1), .shift .sll .d .t3 .t3 8,
   .logic .or r r .t3]

/-- The low 16 bits of `r` to subkey `k` of the schedule at `a1`, low byte
first, clobbering `r`. -/
def storeKey (r : Reg) (k : Nat) : List Instr :=
  [.store .b r .a1 (2 * k), .shift .srl .d r r 8, .store .b r .a1 (2 * k + 1)]

/-! ## Key expansion -/

/-- The half (`a2`, the high one, or `a3`) holding subkey `8j + i`'s window. -/
def half (i : Nat) : Reg := if i < 4 then .a2 else .a3

/-- Subkey `8j + i`, from its window at bit `16 (3 - i % 4)` of its half. -/
def expandSub (j i : Nat) : List Instr :=
  .shift .srl .d .t0 (half i) (16 * (3 - i % 4)) :: storeKey .t0 (8 * j + i)

/-- `a2 a3 := (a2 a3) rotated left by 25 bits` (through `t0`, `t1`). -/
def rotate : List Instr :=
  [.shift .srl .d .t0 .a2 39, .shift .srl .d .t1 .a3 39,
   .shift .sll .d .a2 .a2 25, .shift .sll .d .a3 .a3 25,
   .logic .or .a2 .a2 .t1, .logic .or .a3 .a3 .t0]

/-- The subkeys `8j … min (8j + 7) 51`. -/
def expandGroup (j : Nat) : List Instr :=
  (List.range (if j < 6 then 8 else 4)).flatMap (expandSub j)

def expandKey : Prog isa :=
  .block (Impl.Words.RISCV64.loadBE64 .a2 .t0 .a0 0 ++ Impl.Words.RISCV64.loadBE64 .a3 .t0 .a0 8 ++
    expandGroup 0 ++ (List.range 6).flatMap fun j => rotate ++ expandGroup (j + 1))

/-! ## Inversion -/

/-- `t := (t ⊙ t) ⊙ a` with `t = a4`, `a = a3`, and the count in `a2`. -/
def invStep : List Instr :=
  ([mov .t0 .a4, mov .t1 .a4] : List Instr) ++ mulCode ++
  ([mov .t0 .t1, mov .t1 .a3] : List Instr) ++ mulCode ++
  ([mov .a4 .t1, .addi .a2 .a2 (-1)] : List Instr)

/-- Decryption subkey `n` into `t1`, zero-extended. -/
def invWord (n : Nat) : Prog isa :=
  match invOp n with
  | (.copy, k) => .block (loadKey .t1 k)
  | (.neg, k) => .block (loadKey .a3 k ++
      ([.li .t1 0, .sub .t1 .t1 .a3, .logic .and .t1 .t1 .t2] : List Instr))
  | (.inv, k) => .seq (.block (loadKey .a3 k ++ ([mov .a4 .a3, .li .a2 15] : List Instr)))
      (.seq (.loop (.block invStep) (.nonzero .a2)) (.block [mov .t1 .a4]))

def invertKey : Prog isa :=
  .seq (.block setMask)
    ((List.range 52).foldr (fun n rest => .seq (invWord n) (.seq (.block (storeKey .t1 n)) rest))
      (.block []))

/-! ## ECB -/

/-- `r := r ⊙ subkey k`. -/
def mulKey (r : Reg) (k : Nat) : List Instr :=
  ([mov .t0 r] : List Instr) ++ loadKey .t1 k ++ mulCode ++ ([mov r .t1] : List Instr)

/-- `r := r ⊞ subkey k`, zero-extended. -/
def addKey (r : Reg) (k : Nat) : List Instr :=
  loadKey .t1 k ++ ([.add r r .t1, .logic .and r r .t2] : List Instr)

/-- Round `j` (0–7), with subkeys `6j … 6j + 5`, on `a3`–`a6`. -/
def round (j : Nat) : List Instr :=
  let o := 6 * j
  mulKey .a3 o ++ mulKey .a6 (o + 3) ++ addKey .a4 (o + 1) ++ addKey .a5 (o + 2) ++
  ([.logic .xor .t0 .a3 .a5] : List Instr) ++ loadKey .t1 (o + 4) ++
  mulCode ++
  ([mov .a7 .t1, .logic .xor .t0 .a4 .a6, .add .t0 .t0 .a7] : List Instr) ++ loadKey .t1 (o + 5) ++
  mulCode ++
  ([.add .a7 .a7 .t1, .logic .and .a7 .a7 .t2,
   .logic .xor .a3 .a3 .t1, .logic .xor .a5 .a5 .t1,
   .logic .xor .a4 .a4 .a7, .logic .xor .a6 .a6 .a7,
   mov .t0 .a4, mov .a4 .a5, mov .a5 .t0] : List Instr)

/-- Word `k` of the block at `a1` into `r`, big-endian (through `t3`). -/
def loadWord (r : Reg) (k : Nat) : List Instr :=
  [.load .b r .a1 (2 * k), .shift .sll .d r r 8, .load .b .t3 .a1 (2 * k + 1), .logic .or r r .t3]

/-- The block at `a1` into `a3`–`a6`, one big-endian word each. -/
def load : List Instr :=
  loadWord .a3 0 ++ loadWord .a4 1 ++ loadWord .a5 2 ++ loadWord .a6 3

/-- The output transformation (subkeys 48–51), with the middle words
exchanged back: `a5` gets `X₃ ⊞ Z₄₉`, `a4` `X₂ ⊞ Z₅₀`. -/
def output : List Instr :=
  mulKey .a3 48 ++ mulKey .a6 51 ++ addKey .a5 49 ++ addKey .a4 50

/-- The word in `r` to word `k` of the block at `a1`, big-endian (through `t3`). -/
def storeWord (r : Reg) (k : Nat) : List Instr :=
  [.store .b r .a1 (2 * k + 1), .shift .srl .d .t3 r 8, .store .b .t3 .a1 (2 * k)]

/-- `a3, a5, a4, a6` (Y₁ … Y₄) to the block at `a1`. -/
def store : List Instr :=
  storeWord .a3 0 ++ storeWord .a5 1 ++ storeWord .a4 2 ++ storeWord .a6 3

def cryptBlock : List Instr :=
  load ++ (List.range 8).flatMap round ++ output ++ store

def ecb : Prog isa :=
  .seq (.block setMask)
    (.ite (.zero .a2) (.block [])
      (.loop (.block (cryptBlock ++ ([.addi .a1 .a1 8, .addi .a2 .a2 (-1)] : List Instr)))
        (.nonzero .a2)))

end VG.Impl.Idea.RISCV64
