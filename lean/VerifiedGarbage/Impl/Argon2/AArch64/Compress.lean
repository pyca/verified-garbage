module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Argon2 compression G on ARM64

Baseline instructions; no additional CPU feature is required. Inputs are x0
and x1, output x2, scratch x3. Scratch holds R at offset 0 and its permuted
copy at offset 1024. Each row or column is loaded into sixteen registers
(x0–x2, x4–x16), permuted there with x17 as the only temporary, and stored
back; the output pointer waits in v16 meanwhile. Every address is a public
pointer plus a fixed offset; there are no branches, calls, stack accesses,
or writes to callee-saved registers.
-/

@[expose] public section

namespace VG.Impl.Argon2.AArch64

open VG.AArch64

/-- BlaMka addition `a ← a + b + 2 · lo(a) · lo(b)`: each UMADDL adds the
product of the low halves to one operand, `t` to `b` and `a` to itself. -/
def addMul (a b t : Reg) : List Instr := [.umaddl t a b b, .umaddl a a b a, .add .x a a t]

/-- Half of GB, parameterized by its two rotation counts. -/
def halfGB (a b c d t : Reg) (r1 r2 : Nat) : List Instr :=
  addMul a b t ++
  ([.logic .eor .x d d a, .ror .x d d r1] : List Instr) ++
  addMul c d t ++
  ([.logic .eor .x b b c, .ror .x b b r2] : List Instr)

/-- GB on registers `a`–`d`, with the temporary `t`. -/
def gb (a b c d t : Reg) : List Instr := halfGB a b c d t 32 24 ++ halfGB a b c d t 16 63

/-- The sixteen registers holding a row or column. -/
def lanes : Vector Reg 16 :=
  #v[.x0, .x1, .x2, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16]

/-- The register of word `j` of a row or column. -/
def lane (j : Fin 16) : Reg := lanes[j]

/-- GB on words `a,b,c,d` of the row or column in registers. -/
def gbOn (a b c d : Fin 16) : Prog isa := .block (gb (lane a) (lane b) (lane c) (lane d) .x17)

/-- P on the sixteen registers. -/
def permute : Prog isa :=
  .seq (gbOn 0 4 8 12) <| .seq (gbOn 1 5 9 13) <|
  .seq (gbOn 2 6 10 14) <| .seq (gbOn 3 7 11 15) <|
  .seq (gbOn 0 5 10 15) <| .seq (gbOn 1 6 11 12) <|
  .seq (gbOn 2 7 8 13) (gbOn 3 4 9 14)

/-- Load word `j` of the row or column selected by `index` from the permuted
scratch block. -/
def loadWord (index : Fin 16 → Fin 128) (j : Fin 16) : Instr :=
  .ldr .x (lane j) .x3 (1024 + 8 * (index j).val)

/-- Store word `j` of the row or column back. -/
def storeWord (index : Fin 16 → Fin 128) (j : Fin 16) : Instr :=
  .str .x (lane j) .x3 (1024 + 8 * (index j).val)

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  .seq (.block ((List.finRange 16).map (loadWord index))) <|
  .seq permute (.block ((List.finRange 16).map (storeWord index)))

/-- Copy one word of X XOR Y into both scratch blocks. -/
def initWord (i : Nat) : List Instr := [
  .ldr .x .x8 .x0 (8 * i), .ldr .x .x9 .x1 (8 * i),
  .logic .eor .x .x8 .x8 .x9,
  .str .x .x8 .x3 (8 * i), .str .x .x8 .x3 (1024 + 8 * i)]

/-- XOR the original R into the permuted word and write the output. -/
def finishWord (i : Nat) : List Instr := [
  .ldr .x .x8 .x3 (1024 + 8 * i), .ldr .x .x9 .x3 (8 * i),
  .logic .eor .x .x8 .x8 .x9, .str .x .x8 .x2 (8 * i)]

/-- The complete compression function. The input pointers are `x0,x1`,
the output pointer is `x2`, and scratch is `x3`. -/
def compress : Prog isa :=
  .seq (.block ((List.range 128).flatMap initWord)) <|
  .seq (.block [.vop (.dup .d2 .v16 .x2)]) <|
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  .seq ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block [])) <|
  .seq (.block [.umov .x .x2 .v16 0]) <|
  .block ((List.range 128).flatMap finishWord)

end VG.Impl.Argon2.AArch64
