module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Argon2 compression G on PPC64LE

`vg_argon2_compress(x = r3, y = r4, out = r5, scratch = r6)`: the AArch64
implementation (`Impl/Argon2/AArch64/Compress.lean`), one word at a time.
`scratch` holds R at offset 0, its permuted copy at offset 1024, and the
caller's `r14`–`r22` at offset 2048. Each row or column is loaded into
sixteen registers (`r3`, `r4`, `r7`–`r12`, `r14`–`r21`), permuted there with
`r0` and `r22` as temporaries, and stored back. The BlaMka addition
`a + b + 2 · lo(a) · lo(b)` takes the low halves with `rotlwi` by 0 (a
32-bit rotation, which clears the high half), multiplies them with `mulld`
and adds the product twice. Every address is a public pointer plus a fixed
offset; there are no branches, calls or stack accesses.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE

open VG.PPC64LE

/-- BlaMka addition `a ← a + b + 2 · lo(a) · lo(b)`, with the temporaries
`t` and `u`. -/
def addMul (a b t u : Reg) : List Instr :=
  [.rotr .w t a 0, .rotr .w u b 0, .mul t t u, .add a a b, .add a a t, .add a a t]

/-- Half of GB, parameterized by its two rotation counts. -/
def halfGB (a b c d t u : Reg) (r1 r2 : Nat) : List Instr :=
  addMul a b t u ++
  ([.logic .xor d d a, .rotr .d d d r1] : List Instr) ++
  addMul c d t u ++
  ([.logic .xor b b c, .rotr .d b b r2] : List Instr)

/-- GB on registers `a`–`d`, with the temporaries `t` and `u`. -/
def gb (a b c d t u : Reg) : List Instr := halfGB a b c d t u 32 24 ++ halfGB a b c d t u 16 63

/-- The sixteen registers holding a row or column. -/
def lanes : Vector Reg 16 :=
  #v[.r3, .r4, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21]

/-- The register of word `j` of a row or column. -/
def lane (j : Fin 16) : Reg := lanes[j]

/-- GB on words `a,b,c,d` of the row or column in registers. -/
def gbOn (a b c d : Fin 16) : Prog isa := .block (gb (lane a) (lane b) (lane c) (lane d) .r0 .r22)

/-- P on the sixteen registers. -/
def permute : Prog isa :=
  .seq (gbOn 0 4 8 12) <| .seq (gbOn 1 5 9 13) <|
  .seq (gbOn 2 6 10 14) <| .seq (gbOn 3 7 11 15) <|
  .seq (gbOn 0 5 10 15) <| .seq (gbOn 1 6 11 12) <|
  .seq (gbOn 2 7 8 13) (gbOn 3 4 9 14)

/-- Load word `j` of the row or column selected by `index` from the permuted
scratch block. -/
def loadWord (index : Fin 16 → Fin 128) (j : Fin 16) : Instr :=
  .load .d (lane j) .r6 (1024 + 8 * (index j).val)

/-- Store word `j` of the row or column back. -/
def storeWord (index : Fin 16 → Fin 128) (j : Fin 16) : Instr :=
  .store .d (lane j) .r6 (1024 + 8 * (index j).val)

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  .seq (.block ((List.finRange 16).map (loadWord index))) <|
  .seq permute (.block ((List.finRange 16).map (storeWord index)))

/-- The nonvolatile registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r14, 2048), (.r15, 2056), (.r16, 2064), (.r17, 2072), (.r18, 2080), (.r19, 2088),
    (.r20, 2096), (.r21, 2104), (.r22, 2112)]

def save : List Instr := saved.map fun (r, d) => .store .d r .r6 d

def restore : List Instr := saved.map fun (r, d) => .load .d r .r6 d

/-- Copy word `i` of X XOR Y into both scratch blocks. -/
def initWord (i : Nat) : List Instr := [
  .load .d .r0 .r3 (8 * i), .load .d .r22 .r4 (8 * i), .logic .xor .r0 .r0 .r22,
  .store .d .r0 .r6 (8 * i), .store .d .r0 .r6 (1024 + 8 * i)]

/-- XOR the original R into a permuted word and write it to the output. -/
def finishWord (i : Nat) : List Instr := [
  .load .d .r0 .r6 (1024 + 8 * i), .load .d .r22 .r6 (8 * i), .logic .xor .r0 .r0 .r22,
  .store .d .r0 .r5 (8 * i)]

/-- The complete compression function. -/
def compress : Prog isa :=
  .seq (.block (save ++ (List.range 128).flatMap initWord)) <|
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  .seq ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block [])) <|
  .block ((List.range 128).flatMap finishWord ++ restore)

end VG.Impl.Argon2.PPC64LE
