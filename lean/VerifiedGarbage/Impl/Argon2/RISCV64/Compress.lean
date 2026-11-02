module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Argon2 compression G on RISC-V

`vg_argon2_compress(x = a0, y = a1, out = a2, scratch = a3)`, an internal
function: the PPC64LE implementation (`Impl/Argon2/PPC64LE/Compress.lean`),
for RV64I with the M extension, which has no rotation. Its caller passes
8-byte aligned pointers. `scratch` holds R at offset 0, its permuted copy at
offset 1024, and the caller's `s0`–`s4` at offset 2048, addressed from
`t0 = scratch + 2040` (offsets are below 2048). Each row or column is loaded
into sixteen registers (`t0`–`t4`, `a0`, `a1`, `a4`–`a7`, `s0`–`s4`),
permuted there with `t5` and `t6` as temporaries, and stored back.

* The BlaMka addition `a + b + 2 · lo(a) · lo(b)` shifts both left by 32
  bits and takes the high 64 bits of their product (`mulhu`), which is
  `lo(a) · lo(b)`, and adds it twice.
* A rotation right by `r` is a right shift by `r` into `t5` and a left shift
  by `64 - r`, combined by `or`.

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

/-- Half of GB, parameterized by its two rotation counts. -/
def halfGB (a b c d t u : Reg) (r1 r2 : Nat) : List Instr :=
  addMul a b t u ++ (.logic .xor d d a :: rot d t r1) ++
  addMul c d t u ++ (.logic .xor b b c :: rot b t r2)

/-- GB on registers `a`–`d`, with the temporaries `t` and `u`. -/
def gb (a b c d t u : Reg) : List Instr := halfGB a b c d t u 32 24 ++ halfGB a b c d t u 16 63

/-- The sixteen registers holding a row or column. -/
def lanes : Vector Reg 16 :=
  #v[.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a4, .a5, .a6, .a7, .s0, .s1, .s2, .s3, .s4]

/-- The register of word `j` of a row or column. -/
def lane (j : Fin 16) : Reg := lanes[j]

/-- GB on words `a,b,c,d` of the row or column in registers. -/
def gbOn (a b c d : Fin 16) : Prog isa := .block (gb (lane a) (lane b) (lane c) (lane d) .t5 .t6)

/-- P on the sixteen registers. -/
def permute : Prog isa :=
  .seq (gbOn 0 4 8 12) <| .seq (gbOn 1 5 9 13) <|
  .seq (gbOn 2 6 10 14) <| .seq (gbOn 3 7 11 15) <|
  .seq (gbOn 0 5 10 15) <| .seq (gbOn 1 6 11 12) <|
  .seq (gbOn 2 7 8 13) (gbOn 3 4 9 14)

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
def saved : List (Reg × Nat) := [(.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40)]

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
