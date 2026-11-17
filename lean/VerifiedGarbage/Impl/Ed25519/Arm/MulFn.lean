module

public import VerifiedGarbage.Impl.Ed25519.Arm.Word
public import VerifiedGarbage.Spec.X25519

/-!
# `vg_gf25519_r16_mul` on ARMv7

`vg_gf25519_r16_mul(ws, o, a, b)` (`Proof/X25519/Field16Contract.lean`; AAPCS: `ws`
in `r0`, the offsets in `r1`–`r3`) runs the product of the inlined code
(`mul`, from X25519's ARMv7 product: row by row, with only the low 32-bit
`mul`, then `lo + 38 hi` and the carry folded in twice), but with its
operands and its result through pointers, since their offsets are
arguments: `r10` to the limb of `a` of the current row, `r11` to `b`, and
`r8`, then `r9`, to `o`. The product's limbs are at `ACC`, its own working
space, and the callee-saved registers it changes (`r4`–`r11`) are saved at
`SAVE` and restored, so that it needs no stack. It writes neither `r12` nor
`lr`.

Every address is `ws` plus a constant or a public offset, and the only
branch is the rows' loop: only the pointer and the offsets, which are
public, may affect timing.

`vg_gf25519_r16_mul_umaal`, for CPUs with `umaal` (`hi:lo := n m + hi + lo`,
which cannot overflow), is the same operation on the same limbs (`mulBodyU`):
the operands' limbs are packed in pairs into eight 32-bit words, the second
operand's in the low words of `ACC` (`packU`) and the first's a word a row,
and the product is accumulated row by row in the sixteen words at `ACC + 64`,
each product a load of the two words, one `umaal` and a store (`rowStepU`),
the row's carry being its next word. Then `lo + 38 hi` in words, a chain of
`umaal`s (`foldStepU`), and its carry out, times 38, added as the words are
split into the result's limbs (`splitStepU`); what that carries out, 0 or 1,
is added as 38 to limb 0, which is then small. It changes `r1`–`r9` only, so
that the same code, after its offsets are set, is the inlined product too
(`mulIn`). The functions built with the flag `umaal` multiply with it, and
their names end in `_umaal` (`suffix`).
-/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

open VG.Arm
open VG.Impl.X25519.Arm (mulSrc)

/-- Where `vg_gf25519_r16_mul` saves the callee-saved registers it changes. -/
def mulSaved : List (Reg × Nat) :=
  [(.r4, SAVE), (.r5, SAVE + 4), (.r6, SAVE + 8), (.r7, SAVE + 12), (.r8, SAVE + 16),
    (.r9, SAVE + 20), (.r10, SAVE + 24), (.r11, SAVE + 28)]

/-- The pointers to `o` (`r8`), `a` (`r10`) and `b` (`r11`), the mask of a limb, the product's
limbs zero, and the rows' base and count. -/
def mulSetup : List Instr :=
  [.dp .add .r8 .r0 (.reg .r1), .dp .add .r10 .r0 (.reg .r2), .dp .add .r11 .r0 (.reg .r3),
    .movw .r6 0xffff] ++ zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 16)]

/-- Limb `j` of a row (`r7` = the base plus `4 i`, `a_i` in `r1`), into `r3`:
`a_i b_j + acc[i + j]`, `b` at `r11`. -/
def mulRowSrc (j : Nat) : List Instr :=
  [.ldr .r2 .r11 (4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * j), .dp .add .r3 .r3 (.reg .r2)]

/-- Row `i` of the product: `acc[i, i + 17) = acc[i, i + 16) + a_i · b`, `a_i` at `r10`. -/
def mulRow : List Instr :=
  [.ldr .r1 .r10 0, .mov .r5 (.imm 0)] ++ pass .r7 ACC mulRowSrc ++
    [.str .r5 .r7 (ACC + 64), .dp .add .r7 .r7 (.imm 4), .dp .add .r10 .r10 (.imm 4),
      .subs .r9 .r9 (.imm 1)]

/-- Limb `k` of the result at `r9`, into `r3`. -/
def mulTailSrc (k : Nat) : List Instr := [.ldr .r3 .r9 (4 * k)]

/-- `lo + 38 hi` into the limbs at `o` (`r9`), the carry out folded in as 38 times itself,
twice. -/
def mulFinal : List Instr :=
  [.mov .r9 (.reg .r8), .mov .r8 (.imm 38), .mov .r5 (.imm 0)] ++ pass .r9 0 (mulSrc ACC) ++
    [.mul .r5 .r5 .r8] ++ pass .r9 0 mulTailSrc ++
    [.mul .r5 .r5 .r8, .ldr .r3 .r9 0, .dp .add .r3 .r3 (.reg .r5), .str .r3 .r9 0]

/-- The product of the elements at the offsets in `r2` and `r3` into the one at the offset in
`r1`. -/
def mulBody : Prog isa :=
  .seq (.block mulSetup) (.seq (.loop (.block mulRow) .ne) (.block mulFinal))

/-! ## The product with `umaal` -/

/-- Word `j` of the second operand (at `r9`), limbs `2j` and `2j + 1` packed, into word `j` of
`ACC`. -/
def packU (j : Nat) : List Instr :=
  [.ldr .r2 .r9 (8 * j), .ldr .r3 .r9 (8 * j + 4), .dp .add .r2 .r2 (.shifted .r3 .lsl 16),
    .str .r2 .r0 (ACC + 4 * j)]

/-- The pointers to `o` (`r8`), `a` (`r5`) and `b` (`r9`), the second operand packed, the
product's low eight words zero, and the rows' base and count. -/
def mulSetupU : List Instr :=
  ([.dp .add .r8 .r0 (.reg .r1), .dp .add .r5 .r0 (.reg .r2), .dp .add .r9 .r0 (.reg .r3)] : List Instr) ++
    (List.range 8).flatMap packU ++ ([.mov .r3 (.imm 0)] : List Instr) ++ storeN .r3 (ACC + 64) 8 ++
    ([.mov .r7 (.reg .r0), .mov .r9 (.imm 8)] : List Instr)

/-- One product of a row: the row's word of the first operand, in `r1`, times word `j` of the
second, added to word `j` of the product at `r7` with the carry `r4`. -/
def rowStepU (j : Nat) : List Instr :=
  [.ldr .r2 .r0 (ACC + 4 * j), .ldr .r3 .r7 (ACC + 64 + 4 * j), .umaal .r3 .r4 .r1 .r2,
    .str .r3 .r7 (ACC + 64 + 4 * j)]

/-- A row: the word of the first operand at `r5`, two limbs packed, times the second operand,
added to the product at `r7`; then `r7` moves up a word, `r5` two limbs, and `r9` counts the rows
down. -/
def rowU : List Instr :=
  ([.ldr .r1 .r5 0, .ldr .r2 .r5 4, .dp .add .r1 .r1 (.shifted .r2 .lsl 16), .mov .r4 (.imm 0)] : List Instr) ++
    (List.range 8).flatMap rowStepU ++
    ([.str .r4 .r7 (ACC + 96), .dp .add .r7 .r7 (.imm 4), .dp .add .r5 .r5 (.imm 8),
      .subs .r9 .r9 (.imm 1)] : List Instr)

/-- Word `q` of `lo + 38 hi` (38 in `r8`, the carry in `r4`), back into word `q` of the product. -/
def foldStepU (q : Nat) : List Instr :=
  [.ldr .r3 .r0 (ACC + 64 + 4 * q), .ldr .r2 .r0 (ACC + 96 + 4 * q), .umaal .r3 .r4 .r8 .r2,
    .str .r3 .r0 (ACC + 64 + 4 * q)]

/-- Word `q` of that sum plus the carry `r4` (zero in `r2`), as limbs `2q` and `2q + 1` of the
result at `r9` (the mask of a limb in `r6`). -/
def splitStepU (q : Nat) : List Instr :=
  [.ldr .r3 .r0 (ACC + 64 + 4 * q), .umaal .r3 .r4 .r2 .r2, .dp .and .r1 .r3 (.reg .r6),
    .str .r1 .r9 (8 * q), .mov .r3 (.shifted .r3 .lsr 16), .str .r3 .r9 (8 * q + 4)]

/-- `lo + 38 hi` in words; then 38 times its carry out added as the words are split into the limbs
at `o` (`r9`); then 38 times what that carries out, 0 or 1, into limb 0. -/
def mulFinalU : List Instr :=
  ([.mov .r9 (.reg .r8), .mov .r8 (.imm 38), .movw .r6 0xffff, .mov .r4 (.imm 0)] : List Instr) ++
    (List.range 8).flatMap foldStepU ++ ([.mul .r4 .r4 .r8, .mov .r2 (.imm 0)] : List Instr) ++
    (List.range 8).flatMap splitStepU ++
    ([.mul .r4 .r4 .r8, .ldr .r3 .r9 0, .dp .add .r3 .r3 (.reg .r4), .str .r3 .r9 0] : List Instr)

/-- The product of the elements at the offsets in `r2` and `r3` into the one at the offset in
`r1`, with `umaal`: it changes `r1`–`r9`. -/
def mulBodyU : Prog isa :=
  .seq (.block mulSetupU) (.seq (.loop (.block rowU) .ne) (.block mulFinalU))

/-- The suffix of a function's name: `_umaal` for the functions that multiply with the
instruction `umaal` (the flag `umaal`). -/
def suffix (umaal : Bool) : String := if umaal then "_umaal" else ""

/-- `vg_gf25519_r16_mul` and, with the flag `umaal`, `vg_gf25519_r16_mul_umaal`: the product, the
registers it changes saved and restored. -/
def mulFn (umaal : Bool) : Prog isa :=
  .seq (.block (mulSaved.map fun p => .str p.1 .r0 p.2))
    (.seq (if umaal then mulBodyU else mulBody) (.block (mulSaved.map fun p => .ldr p.1 .r0 p.2)))

/-- The offsets of a product's result and operands into `r1`–`r3`. -/
def mulArgs (o a b : Nat) : List Instr :=
  [.movw .r1 (BitVec.ofNat 16 o), .movw .r2 (BitVec.ofNat 16 a), .movw .r3 (BitVec.ofNat 16 b)]

/-- A call of the product: `[o] = [a] · [b]`. -/
def mulCall (umaal : Bool) (o a b : Nat) : Prog isa :=
  .seq (.block (mulArgs o a b)) (.call ("vg_gf25519_r16_mul" ++ suffix umaal) (mulFn umaal))

/-- `[o] = [a] · [b]` inlined (`o` may be `a` or `b`): with the flag `umaal`, `mulBodyU` at these
offsets. -/
def mulIn (umaal : Bool) (o a b : Nat) : Prog isa :=
  if umaal then .seq (.block (mulArgs o a b)) mulBodyU else mul o a b

end VG.Impl.Ed25519.Arm
