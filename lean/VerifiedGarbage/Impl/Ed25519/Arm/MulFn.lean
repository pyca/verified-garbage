import VerifiedGarbage.Impl.Ed25519.Arm.Word
import VerifiedGarbage.Spec.X25519.Field16

/-!
# `vg_gf25519_r16_mul` on ARMv7

`vg_gf25519_r16_mul(ws, o, a, b)` (`Spec/X25519/Field16.lean`; AAPCS: `ws`
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
-/

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

/-- `vg_gf25519_r16_mul`: `mulBody`, the registers it changes saved and restored. -/
def mulFn : Prog isa :=
  .seq (.block (mulSaved.map fun p => .str p.1 .r0 p.2))
    (.seq mulBody (.block (mulSaved.map fun p => .ldr p.1 .r0 p.2)))

/-- A call of `vg_gf25519_r16_mul`: `[o] = [a] · [b]`. -/
def mulCall (o a b : Nat) : Prog isa :=
  .seq (.block [.movw .r1 (BitVec.ofNat 16 o), .movw .r2 (BitVec.ofNat 16 a),
    .movw .r3 (BitVec.ofNat 16 b)]) (.call Spec.X25519.Field16.mulApi.name mulFn)

end VG.Impl.Ed25519.Arm
