import VerifiedGarbage.Impl.X448.Arm
import VerifiedGarbage.Impl.X25519.Arm

/-!
# Ed448 scalar arithmetic on ARMv7

Arithmetic modulo the subgroup order `L = 2^446 - c` (`c < 2^224`), on a
remainder of twenty-eight 16-bit limbs in 32-bit words of the working space,
X448's representation on this target. The only multiplication is the low
word of `mul`, of two 16-bit numbers.

Reduction consumes the input sixteen bits at a time, from the top: the
remainder `r < L` (limbs `r₀, …, r₂₇`, so `r₂₇ < 2^14`) becomes
`v = 2^16 r + w` for the next chunk `w`, which is `h 2^446 + l` with
`h = r₂₆ >> 14 + 4 r₂₇ < 2^16` and `l` the limbs `w, r₀, …, r₂₅,
r₂₆ mod 2^14`; so `v ≡ l + h c` (mod L) since `2^446 ≡ c`, and `l + h c`
is below `2^446 + 2^240 < 2L` (`fold`, into `TF`). One carry pass computes
it: `h` times the fourteen limbs of `c`, each product and limb below `2^32`
with the carry (Knuth's algorithm M). A conditional subtraction of `L`
(`reduceT`) leaves `v mod L`: `K = 2^448 - L` added to `TF`, into the
remainder, carries out of 448 bits exactly when `v ≥ L`, and the sum or
`TF` is selected with the mask `-carry`.

Multiply-add reduces its three inputs, multiplies two of them with X448's
rows (`row`, into X448's `ACC`), reduces the product's fifty-six limbs, and
adds the third, with a last conditional subtraction.

Every step runs for all limbs, independent of their values: no branch but on
the loop counter `r10`, and every address a pointer plus a constant or the
counter. The working space's base is in `r0` and the limb mask `0xffff` in
`r6`; the callee-saved registers are saved in its first 32 bytes, and the
addresses of the output and the arguments from byte 32 (`OUT`).
-/

namespace VG.Impl.Ed448.Arm

open VG.Arm
open VG.Impl.X448.Arm (carryPass row mulPre ACC)

/-! ## The layout of the working space -/

/-- The output's address, and those of the arguments `r`, `k` and `s` of
multiply-add. -/
def OUT : Nat := 32
/-- The folded value `l + h c`. -/
def TF : Nat := 64
/-- The remainder of reduction, and of the product in multiply-add. -/
def RA : Nat := 192
/-- The reduced `k`, `s` and `r` of multiply-add. -/
def SK : Nat := 320
def SS : Nat := 448
def SR : Nat := 576

/-! ## Constants -/

/-- The 16-bit limbs of `c = 2^446 - L`, lowest first. -/
def cLimbs : List Nat :=
  [0xbb0d, 0x54a7, 0x3d6d, 0xdc87, 0x70aa, 0x723a, 0x3d8d, 0xde93, 0xc96f, 0x5129, 0x24b6,
    0x3bb1, 0xdc16, 0x8335]

/-- Limb `k` of `c`. -/
def cLimb (k : Nat) : Nat := cLimbs.getD k 0

/-- Limb `k` of `K = 2^448 - L = 3 · 2^446 + c`. -/
def kLimb (k : Nat) : Nat := if k = 27 then 0xc000 else cLimb k

/-! ## One chunk -/

/-- `h = r₂₆ >> 14 + 4 r₂₇` into `r1`, for the remainder at `o`; no carry
in `r5`. -/
def foldHead (o : Nat) : List Instr :=
  [.ldr .r1 .r0 (o + 104), .mov .r1 (.shifted .r1 .lsr 14), .ldr .r2 .r0 (o + 108),
    .dp .add .r1 .r1 (.shifted .r2 .lsl 2), .mov .r5 (.imm 0)]

/-- Limb `k` of `l + h c` before carrying, into `r3`: the chunk `w` (in
`r11`) or the limb below of the remainder at `o` (the top one masked to 14
bits), plus `h` (in `r1`) times limb `k` of `c` below limb 14. -/
def foldSrc (o k : Nat) : List Instr :=
  if k = 0 then
    [.movw .r2 (BitVec.ofNat 16 (cLimb 0)), .mul .r2 .r1 .r2, .dp .add .r3 .r11 (.reg .r2)]
  else if k < 14 then
    [.ldr .r3 .r0 (o + 4 * (k - 1)), .movw .r2 (BitVec.ofNat 16 (cLimb k)), .mul .r2 .r1 .r2,
      .dp .add .r3 .r3 (.reg .r2)]
  else if k < 27 then [.ldr .r3 .r0 (o + 4 * (k - 1))]
  else [.ldr .r3 .r0 (o + 104), .mov .r3 (.shifted .r3 .lsl 18), .mov .r3 (.shifted .r3 .lsr 18)]

/-- `2^16 r + w`, reduced below `2L`, into `TF`. -/
def fold (o : Nat) : List Instr := foldHead o ++ carryPass .r0 TF (foldSrc o)

/-- Limb `k` of `TF + K` before carrying, into `r3`. -/
def csubSrc (k : Nat) : List Instr :=
  if k < 14 ∨ k = 27 then
    [.ldr .r3 .r0 (TF + 4 * k), .movw .r2 (BitVec.ofNat 16 (kLimb k)), .dp .add .r3 .r3 (.reg .r2)]
  else [.ldr .r3 .r0 (TF + 4 * k)]

/-- Limb `k` of the remainder at `o`: itself under the mask `r9`, else limb
`k` of `TF`. -/
def selectStep (o k : Nat) : List Instr :=
  [.ldr .r3 .r0 (o + 4 * k), .ldr .r2 .r0 (TF + 4 * k), .dp .eor .r3 .r3 (.reg .r2),
    .dp .and .r3 .r3 (.reg .r9), .dp .eor .r3 .r3 (.reg .r2), .str .r3 .r0 (o + 4 * k)]

/-- `TF` (below `2L`) reduced modulo `L` into the remainder at `o`: `TF + K`
into `o`, carrying out of 448 bits (`r5`) exactly when `TF ≥ L`, and then
the sum if it carried or `TF`. -/
def reduceT (o : Nat) : List Instr :=
  [.mov .r5 (.imm 0)] ++ carryPass .r0 o csubSrc ++
    [.mov .r9 (.imm 0), .dp .sub .r9 .r9 (.reg .r5)] ++ (List.range 28).flatMap (selectStep o)

/-- The remainder at `o` and the chunk in `r11` folded and reduced. -/
def step (o : Nat) : List Instr := fold o ++ reduceT o

/-! ## Reducing an input -/

/-- The next two bytes from the top of the input at `r12` into `r11`
(`r10` counts its bytes down). -/
def readBytes : List Instr :=
  [.dp .sub .r10 .r10 (.imm 2), .dp .add .r2 .r12 (.reg .r10), .ldrb .r11 .r2 0, .ldrb .r3 .r2 1,
    .dp .add .r11 .r11 (.shifted .r3 .lsl 8)]

def byteStep (o : Nat) : List Instr := readBytes ++ step o ++ [.cmp .r10 (.imm 0)]

/-- The remainder at `o` set to zero. -/
def zeroR (o : Nat) : List Instr :=
  .mov .r3 (.imm 0) :: (List.range 28).flatMap fun k => [.str .r3 .r0 (o + 4 * k)]

/-- The remainder at `o` of the 114 bytes at `r12`. -/
def reduce114 (o : Nat) : Prog isa :=
  .seq (.block (zeroR o ++ [.mov .r10 (.imm 114)])) (.loop (.block (byteStep o)) .ne)

/-- The remainder at `o` of the 57 bytes at `r12`: their top byte, then the
twenty-eight chunks below it. -/
def reduce57 (o : Nat) : Prog isa :=
  .seq (.block (zeroR o ++ [.ldrb .r3 .r12 56, .str .r3 .r0 o, .mov .r10 (.imm 56)]))
    (.loop (.block (byteStep o)) .ne)

/-! ## Entry and exit -/

/-- The callee-saved registers `r4`–`r11`. -/
abbrev savedReg : Nat → Reg := Impl.X25519.Arm.savedReg

/-- The callee-saved registers saved at `[b]`. -/
def saveAt (b : Reg) : List Instr := (List.range 8).flatMap fun i => [.str (savedReg i) b (4 * i)]

/-- The callee-saved registers restored from the working space. -/
def restore : List Instr := (List.range 8).flatMap fun i => [.ldr (savedReg i) .r0 (4 * i)]

/-- Limb `k` of the remainder at `o` as two bytes at `r12`. -/
def packLimb (o k : Nat) : List Instr :=
  [.ldr .r3 .r0 (o + 4 * k), .strb .r3 .r12 (2 * k), .mov .r3 (.shifted .r3 .lsr 8),
    .strb .r3 .r12 (2 * k + 1)]

/-- The remainder at `o` to the 57 bytes at `r12`: twenty-eight limbs and a
zero byte; then the callee-saved registers restored. -/
def output (o : Nat) : List Instr :=
  (List.range 28).flatMap (packLimb o) ++ [.mov .r3 (.imm 0), .strb .r3 .r12 56] ++ restore

/-- `output o` to the output's address, saved at `OUT`. -/
def finish (o : Nat) : List Instr := .ldr .r12 .r0 OUT :: output o

/-- `vg_ed448_scalar_reduce(out = r0, wide = r1, scratch = r2)`. -/
def scalarReduce : Prog isa :=
  .seq (.block (saveAt .r2 ++ [.str .r0 .r2 OUT, .mov .r0 (.reg .r2), .mov .r12 (.reg .r1),
    .movw .r6 0xffff])) <|
  .seq (reduce114 RA) (.block (finish RA))

/-! ## Multiply-add -/

/-- The argument registers. -/
def argReg : Nat → Reg
  | 0 => .r0 | 1 => .r1 | 2 => .r2 | _ => .r3

/-- The working space (the stack argument) into `r12`, the callee-saved
registers and the arguments `out`, `r`, `k` and `s` saved there (from
`OUT`), and its base into `r0`. -/
def mulAddArgs : List Instr :=
  [.ldrSp .r12 0] ++ saveAt .r12 ++ (List.range 4).flatMap (fun i => [.str (argReg i) .r12 (OUT + 4 * i)]) ++
    [.mov .r0 (.reg .r12), .movw .r6 0xffff]

/-- The remainder at `o` of the 57 bytes at the address saved at `off`. -/
def reduceArg (off o : Nat) : Prog isa := .seq (.block [.ldr .r12 .r0 off]) (reduce57 o)

/-- `k`, `s` and `r` (saved at `OUT + 8`, `OUT + 12`, `OUT + 4`) reduced to
`SK`, `SS` and `SR`. -/
def inputs : Prog isa :=
  .seq (reduceArg (OUT + 4 * 2) SK) <| .seq (reduceArg (OUT + 4 * 3) SS) (reduceArg (OUT + 4 * 1) SR)

/-- The product of the remainders at `SK` and `SS`, at `ACC`. -/
def product : Prog isa := .seq (.block mulPre) (.loop (.block (row SK SS)) .ne)

/-- Limb `k` of the product's remainder plus the reduced `r`, into `r3`. -/
def addSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (RA + 4 * k), .ldr .r2 .r0 (SR + 4 * k), .dp .add .r3 .r3 (.reg .r2)]

/-- The next limb of the product from the top into `r11` (`r10` counts its
bytes down). -/
def readLimb : List Instr :=
  [.dp .sub .r10 .r10 (.imm 4), .dp .add .r2 .r0 (.reg .r10), .ldr .r11 .r2 ACC]

def limbStep : List Instr := readLimb ++ step RA ++ [.cmp .r10 (.imm 0)]

/-- The remainder at `RA` of the fifty-six product limbs at `ACC`. -/
def reduceProduct : Prog isa :=
  .seq (.block (zeroR RA ++ [.mov .r10 (.imm 224)])) (.loop (.block limbStep) .ne)

/-- The sum of the product's remainder and the reduced `r`, into `TF`. -/
def addPass : List Instr := [.mov .r5 (.imm 0)] ++ carryPass .r0 TF addSrc

/-- `vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`:
`k mod L` to `SK`, `s mod L` to `SS`, `r mod L` to `SR`; their product's
limbs at `ACC`, reduced to `RA`, plus `SR` into `TF`, reduced. The output's
address is loaded before the product: the rows store through `r7`, an
address the taint analysis does not track. -/
def scalarMulAdd : Prog isa :=
  .seq (.block mulAddArgs) <| .seq inputs <| .seq (.block [.ldr .r12 .r0 OUT]) <| .seq product <|
    .seq reduceProduct <| .block (addPass ++ reduceT RA ++ output RA)

end VG.Impl.Ed448.Arm
