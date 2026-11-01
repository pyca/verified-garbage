module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Word
public import VerifiedGarbage.Spec.X25519

/-!
# `vg_gf25519_r32_mul` on PPC64LE

`vg_gf25519_r32_mul(ws, o, a, b)` (`Proof/X25519/Field32Contract.lean`; ELFv2: `ws`
in `r3`, the offsets in the low words of `r4`–`r6`) runs the product of the
inlined code (`mul`, from X25519's PPC64LE product: row by row, with
`mulld`, then `lo + 38 hi` and the carry folded in twice), but with its
operands and its result through pointers, since their offsets are
arguments: `r10` to the limb of `a` of the current row, `r6` to `b`, and
`r12` to `o`; 38 is in `r0`. The product's limbs are at `ACC`, its own
working space. It uses only volatile registers, and writes neither `r3` nor
`lr`.

Every address is `ws` plus a constant or a public offset, and the only
branch is on the rows' counter, so only `ws` and the offsets can affect
timing.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE

open VG.PPC64LE
open VG.Impl.X25519.PPC64LE (carryStep)

/-- The offsets zero-extended: only their low words are arguments. -/
def mulZext : List Instr := [.rotr .w .r4 .r4 0, .rotr .w .r5 .r5 0, .rotr .w .r6 .r6 0]

/-- The pointers to `o` (`r12`), `a` (`r10`) and `b` (`r6`), 38 in `r0`, the
product's limbs zero, and the rows' base and count. -/
def mulSetup : List Instr :=
  [.add .r12 .r3 .r4, .add .r10 .r3 .r5, .add .r6 .r3 .r6, .li .r0 38, .li .r7 0] ++
  (List.range 8).map (fun k => .store .w .r7 .r3 (ACC + 4 * k)) ++ [.addi .r9 .r3 0, .li .r11 8]

/-- Limb `j` of a row (`r9` = the base plus `4 i`, `a_i` in `r4`), into
`r7`: `a_i b_j + acc[i + j]`, `b` at `r6`. -/
def mulRowSrc (j : Nat) : List Instr :=
  [.load .w .r5 .r6 (4 * j), .mul .r5 .r4 .r5, .load .w .r7 .r9 (ACC + 4 * j), .add .r7 .r7 .r5]

/-- Row `i` of the product: `acc[i, i + 9) = acc[i, i + 8) + a_i · b`, `a_i` at `r10`. -/
def mulRow : List Instr :=
  [.load .w .r4 .r10 0, .li .r8 0] ++ pass .r9 ACC mulRowSrc ++
    [.store .w .r8 .r9 (ACC + 32), .addi .r9 .r9 4, .addi .r10 .r10 4, .subi .r11 .r11 1]

/-- Limb `k` of `lo + 38 hi` for the product at `ACC`, into `r7`. -/
def mulFnSrc (k : Nat) : List Instr :=
  [.load .w .r7 .r3 (ACC + 4 * k), .load .w .r5 .r3 (ACC + 32 + 4 * k), .mul .r5 .r5 .r0,
    .add .r7 .r7 .r5]

/-- Limb `k` of the result at `r12`, into `r7`. -/
def mulTailSrc (k : Nat) : List Instr := [.load .w .r7 .r12 (4 * k)]

/-- `lo + 38 hi` into the limbs at `o` (`r12`), the carry out folded in as
38 times itself, twice. -/
def mulFinal : List Instr :=
  [.li .r8 0] ++ pass .r12 0 mulFnSrc ++ [.mul .r8 .r8 .r0] ++ pass .r12 0 mulTailSrc ++
    [.mul .r8 .r8 .r0, .load .w .r7 .r12 0, .add .r7 .r7 .r8, .store .w .r7 .r12 0]

/-- `vg_gf25519_r32_mul`: the product of the elements at the offsets in
`r5` and `r6` into the one at the offset in `r4`. -/
def mulFn : Prog isa :=
  .seq (.block mulZext)
    (.seq (.block mulSetup) (.seq (.loop (.block mulRow) (.nonzero .d .r11)) (.block mulFinal)))

/-- A call of `vg_gf25519_r32_mul`: `[o] = [a] · [b]`, the working space in
`r6` before and after (the callee keeps it in `r3`). -/
def mulCall (o a b : Nat) : Prog isa :=
  .seq (.block [.addi .r3 .r6 0, .li .r4 o, .li .r5 a, .li .r6 b])
    (.seq (.call "vg_gf25519_r32_mul" mulFn) (.block [.addi .r6 .r3 0]))

end VG.Impl.Ed25519.PPC64LE
