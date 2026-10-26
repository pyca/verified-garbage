module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Argon2 compression G on ARM64

Baseline instructions; no additional CPU feature is required. Inputs are x0
and x1, output x2, scratch x3. Scratch holds R at offset 0 and its permuted
copy at offset 1024; R and the output are computed two words at a time, in
v0 and v1. Each row or column is loaded into sixteen registers
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

/-- Four independent GB chains, advanced one addition or rotation stage at
once. Every BlaMka step consumes `x17` before the next step reuses it. -/
def halfGBs (qs : List (Reg × Reg × Reg × Reg)) (r1 r2 : Nat) : List Instr :=
  qs.flatMap (fun (a, b, _, _) => addMul a b .x17) ++
  qs.flatMap (fun (a, _, _, d) => [.logic .eor .x d d a, .ror .x d d r1]) ++
  qs.flatMap (fun (_, _, c, d) => addMul c d .x17) ++
  qs.flatMap (fun (_, b, c, _) => [.logic .eor .x b b c, .ror .x b b r2])

def gbGroup (qs : List (Reg × Reg × Reg × Reg)) : Prog isa :=
  .block (halfGBs qs 32 24 ++ halfGBs qs 16 63)

/-- P on the sixteen registers, interleaving the four independent chains
within each half-round without additional registers or memory accesses. -/
def permute : Prog isa :=
  .seq (gbGroup [(lane 0, lane 4, lane 8, lane 12),
    (lane 1, lane 5, lane 9, lane 13), (lane 2, lane 6, lane 10, lane 14),
    (lane 3, lane 7, lane 11, lane 15)])
    (gbGroup [(lane 0, lane 5, lane 10, lane 15),
      (lane 1, lane 6, lane 11, lane 12), (lane 2, lane 7, lane 8, lane 13),
      (lane 3, lane 4, lane 9, lane 14)])

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

/-- Copy two words of X XOR Y into both scratch blocks. -/
def initPair (i : Nat) : List Instr := [
  .ldrq .v0 .x0 (16 * i), .ldrq .v1 .x1 (16 * i),
  .vop (.logic .eor .v0 .v0 .v1),
  .strq .v0 .x3 (16 * i), .strq .v0 .x3 (1024 + 16 * i)]

/-- XOR the original R into two permuted words and write the output. -/
def finishPair (i : Nat) : List Instr := [
  .ldrq .v0 .x3 (1024 + 16 * i), .ldrq .v1 .x3 (16 * i),
  .vop (.logic .eor .v0 .v0 .v1), .strq .v0 .x2 (16 * i)]

/-- The complete compression function. The input pointers are `x0,x1`,
the output pointer is `x2`, and scratch is `x3`. -/
def compress : Prog isa :=
  .seq (.block ((List.range 64).flatMap initPair)) <|
  .seq (.block [.vop (.dup .d2 .v16 .x2)]) <|
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  .seq ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block [])) <|
  .seq (.block [.umov .x .x2 .v16 0]) <|
  .block ((List.range 64).flatMap finishPair)

end VG.Impl.Argon2.AArch64
