import VerifiedGarbage.Impl.X25519.Arm
import VerifiedGarbage.Spec.X25519.Field16

/-!
# Multiplication in curve25519's field on ARMv7, as a function

`vg_gf25519_r16_mul(ws, o, a, b)` (`Spec/X25519/Field16.lean`; AAPCS: `ws` in
`r0`, the offsets `o`, `a` and `b` in `r1`–`r3`). It saves the callee-saved
registers it changes (`r4`–`r9` and `lr`) in its own working space (`SAVE`),
needing no stack, keeps `o` in `lr` and points `r8` at `[a]` and `r12` at
`[b]`. Then it runs
X25519's product (`mulAt`) with its operands read through those pointers:
the 32 limbs of `a b`, row by row, in its own working space (`ACC`), each
row's limb of `[a]` through `r8` (which moves up a word a row) and the limbs
of `[b]` through `r12`; then the limbs of `lo + 38 hi` over the low half of
`ACC` (`pass`, which reads each limb's pair before it stores it) and the
carry out folded in (`tail`). Last, it copies the result to `[o]` through
`r12` and restores the registers. It never writes `r0`, `r10` or `r11`, so
a caller's analysis that follows the call keeps them public.

Every address is `ws` or one of the pointers plus a constant or the row
counter, and the only branch is the rows' loop: only the arguments, which are
public, may affect timing.
-/

namespace VG.Impl.X25519.Arm.Field16

open VG.Arm VG.Impl.X25519.Arm

/-- The 32 limbs of the product, the start of the function's own working space. -/
def ACC : Nat := Spec.X25519.Field16.ownAt

/-- Where the function saves the registers it changes: the rest of its own
working space. -/
def SAVE : Nat := ACC + 128

/-- Where the function saves each callee-saved register it changes (`lr`
holds `o` until the copy to `[o]`). -/
def saveSlots : List (Reg × Nat) :=
  [(.r4, SAVE), (.r5, SAVE + 4), (.r6, SAVE + 8), (.r7, SAVE + 12), (.r8, SAVE + 16), (.r9, SAVE + 20),
    (.lr, SAVE + 24)]

/-- The registers stored at their slots. -/
def save : List Instr := saveSlots.map fun p => .str p.1 .r0 p.2

/-- `lr = o`, `r8 = ws + a`, `r12 = ws + b`. -/
def entry : List Instr := [.mov .lr (.reg .r1), .dp .add .r8 .r0 (.reg .r2), .dp .add .r12 .r0 (.reg .r3)]

/-- Limb `j` of row `i` (`r7` = `ws + 4 i`, `a_i` in `r1`) into `r3`:
`a_i b_j + acc[i + j]`, `b_j` through `r12`. -/
def rowSrc (j : Nat) : List Instr :=
  [.ldr .r2 .r12 (4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * j), .dp .add .r3 .r3 (.reg .r2)]

/-- Row `i` of the product, `a_i` through `r8`: `acc[i, i + 17) =
acc[i, i + 16) + a_i · b`. -/
def row : List Instr :=
  [.ldr .r1 .r8 0, .mov .r5 (.imm 0)] ++ pass .r7 ACC rowSrc ++
    [.str .r5 .r7 (ACC + 64), .dp .add .r7 .r7 (.imm 4), .dp .add .r8 .r8 (.imm 4),
      .subs .r9 .r9 (.imm 1)]

/-- The registers saved, the constants, the pointers, `ACC` zeroed and the
row counter. -/
def start : List Instr :=
  save ++ prologue ++ entry ++ zeroAcc ACC ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 16)]

/-- Limb `k` of the result, from `ACC` to `[r12]`. -/
def copyOut (k : Nat) : List Instr := [.ldr .r3 .r0 (ACC + 4 * k), .str .r3 .r12 (4 * k)]

/-- `r12 = ws + o`. -/
def outPtr : List Instr := [.dp .add .r12 .r0 (.reg .lr)]

/-- The saved registers reloaded. -/
def restore : List Instr := saveSlots.map fun p => .ldr p.1 .r0 p.2

/-- `lo + 38 hi` over `ACC`, the carry folded in, copied to `[o]`, and the
registers restored. -/
def finish : List Instr :=
  [.mov .r8 (.imm 38), .mov .r5 (.imm 0)] ++ pass .r0 ACC (mulSrc ACC) ++ tail ACC ++ outPtr ++
    (List.range 16).flatMap copyOut ++ restore

/-- `vg_gf25519_r16_mul`. -/
def mulFn : Prog isa := .seq (.block start) (.seq (.loop (.block row) .ne) (.block finish))

/-- A call of `vg_gf25519_r16_mul` for the offsets `o`, `a` and `b`. -/
def mulCall (o a b : Nat) : Prog isa :=
  .seq (.block [.movw .r1 (BitVec.ofNat 16 o), .movw .r2 (BitVec.ofNat 16 a), .movw .r3 (BitVec.ofNat 16 b)])
    (.call Spec.X25519.Field16.mulApi.name mulFn)

end VG.Impl.X25519.Arm.Field16
