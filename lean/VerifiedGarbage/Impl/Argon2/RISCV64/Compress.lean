module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Argon2 compression G on RISC-V

`vg_argon2_compress(x = a0, y = a1, out = a2, scratch = a3)`, an internal
function: the PPC64LE implementation (`Impl/Argon2/PPC64LE/Compress.lean`),
for RV64I with the M extension, which has no rotation. Its caller passes
8-byte aligned pointers. `scratch` holds R at offset 0, its permuted copy at
offset 1024, and the caller's `s0`–`s5` at offset 2048, addressed from
`t0 = scratch + 2040` (offsets are below 2048). Each row or column is loaded
into sixteen registers (`t0`–`t4`, `a0`, `a1`, `a4`–`a7`, `s0`–`s4`),
permuted there, and stored back. P's four column GBs touch disjoint words,
and so do its four diagonal ones: each step of the four runs for all four at
once (`step4`), so that the four chains of dependent operations are side by
side.

* The BlaMka addition `a + b + 2 · lo(a) · lo(b)` shifts both left by 32
  bits and takes the high 64 bits of their product (`mulhu`), which is
  `lo(a) · lo(b)`, and adds it twice.
  The additions use `t5` and `t6` as temporaries.
* A rotation right by `r` is a right shift by `r` into `s5` and a left shift
  by `64 - r`, combined by `or`. A temporary of its own keeps the order of
  each temporary's uses that of the GBs in turn, which the proof needs.

Every address is a public pointer plus a fixed offset; there are no
branches, calls or stack accesses.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64

open VG.RISCV64

/-- BlaMka addition `a ← a + b + 2 · lo(a) · lo(b)`, with the temporaries
`t` and `u`. -/
def addMul (a b t u : Reg) : List Instr :=
  [.shift .sll .d t a 32, .shift .sll .d u b 32, .mulhu t t u, .add a a b, .add a a t, .add a a t]

/-- `d := d ⋙ r`, through `t`. -/
def rot (d t : Reg) (r : Nat) : List Instr :=
  [.shift .srl .d t d r, .shift .sll .d d d (64 - r), .logic .or d d t]

/-- The sixteen registers holding a row or column. -/
def lanes : Vector Reg 16 :=
  #v[.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a4, .a5, .a6, .a7, .s0, .s1, .s2, .s3, .s4]

/-- The register of word `j` of a row or column. -/
def lane (j : Fin 16) : Reg := lanes[j]

/-- Step `r` of four GBs at once: `a ← a + b + 2 · lo(a) · lo(b); d ← (d ⊕ a) ⋙ r`
for each `(a, b, d)` of `ls`: their additions, then their XORs, then their
rotations, so that the four chains of dependent operations are side by side.
The additions share the temporaries `t5` and `t6`, and the rotations `s5`,
which the core renames. -/
def step4 (ls : List (Fin 16 × Fin 16 × Fin 16)) (r : Nat) : List Instr :=
  ls.flatMap (fun (a, b, _) => addMul (lane a) (lane b) .t5 .t6) ++
  ls.map (fun (a, _, d) => .logic .xor (lane d) (lane d) (lane a)) ++
  ls.flatMap (fun (_, _, d) => rot (lane d) .s5 r)

/-- The four GBs `(a, b, c, d)` of `qs` at once (§3.6, Figure 19). -/
def round4 (qs : List (Fin 16 × Fin 16 × Fin 16 × Fin 16)) : List Instr :=
  step4 (qs.map fun (a, b, _, d) => (a, b, d)) 32 ++ step4 (qs.map fun (_, b, c, d) => (c, d, b)) 24 ++
  step4 (qs.map fun (a, b, _, d) => (a, b, d)) 16 ++ step4 (qs.map fun (_, b, c, d) => (c, d, b)) 63

/-- P's column GBs, and its diagonal ones. -/
def columns : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) := [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]
def diagonals : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) := [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

/-- P on the sixteen registers: its four column GBs at once, then its four diagonal ones. -/
def permute : Prog isa := .block (round4 columns ++ round4 diagonals)

/-- Load word `j` of the row or column selected by `index` from the permuted
scratch block. -/
def loadWord (index : Fin 16 → Fin 128) (j : Fin 16) : Instr :=
  .load .d (lane j) .a3 (1024 + 8 * (index j).val)

/-- Store word `j` of the row or column back. -/
def storeWord (index : Fin 16 → Fin 128) (j : Fin 16) : Instr :=
  .store .d (lane j) .a3 (1024 + 8 * (index j).val)

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  .seq (.block ((List.finRange 16).map (loadWord index))) <|
  .seq permute (.block ((List.finRange 16).map (storeWord index)))

/-- The callee-saved registers we use, and where they are saved, from
`t0 = scratch + 2040`. -/
def saved : List (Reg × Nat) := [(.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48)]

def save : List Instr := .addi .t0 .a3 2040 :: saved.map fun (r, d) => .store .d r .t0 d

def restore : List Instr := .addi .t0 .a3 2040 :: saved.map fun (r, d) => .load .d r .t0 d

/-- Copy word `i` of X XOR Y into both scratch blocks. -/
def initWord (i : Nat) : List Instr := [
  .load .d .t0 .a0 (8 * i), .load .d .t1 .a1 (8 * i), .logic .xor .t0 .t0 .t1,
  .store .d .t0 .a3 (8 * i), .store .d .t0 .a3 (1024 + 8 * i)]

/-- XOR the original R into a permuted word and write it to the output. -/
def finishWord (i : Nat) : List Instr := [
  .load .d .t0 .a3 (1024 + 8 * i), .load .d .t1 .a3 (8 * i), .logic .xor .t0 .t0 .t1,
  .store .d .t0 .a2 (8 * i)]

/-- The complete compression function. -/
def compress : Prog isa :=
  .seq (.block (save ++ (List.range 128).flatMap initWord)) <|
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  .seq ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block [])) <|
  .block ((List.range 128).flatMap finishWord ++ restore)

end VG.Impl.Argon2.RISCV64
