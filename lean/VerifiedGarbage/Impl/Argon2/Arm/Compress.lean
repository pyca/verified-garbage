import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Impl.Blake2.Arm.CompressB

/-!
# Argon2 compression G on ARMv7

`vg_argon2_compress(x = r0, y = r1, out = r2, scratch = r3)`.

* `r3` holds `scratch` throughout. `[0, 1024)` holds R = X XOR Y, and
  `[1024, 2048)` the block P permutes (word `k` at `1024 + 8k`). The caller's
  `r4`–`r11` and our return address (`lr`) are kept in `scratch[2048, 2084)`,
  and `out` in `scratch[2084, 2088)`.
* Each 64-bit word is a pair of 32-bit words, the low one first (as in
  memory), as in BLAKE2b (`Impl/Blake2/Arm/CompressB.lean`, whose exclusive or
  and rotations this uses). GB loads its four words into `r4`–`r11`, computes
  its eight steps in registers, and stores them back; the rotations rename the
  registers, so the code takes each result from where it ends up.
* The model has only the 32-bit `mul` (no `umull`), so `addMul` computes the
  high half of the product of the low halves from four products of 16-bit
  halves (`mulHi`), and its low half with one more `mul`; five temporaries
  (`r0`–`r2`, `lr` and one of `r6`, `r11`, `r12`) hold the partial products.
* Every address is `r0`–`r3` plus a constant, and there are no branches.
-/

namespace VG.Impl.Argon2.Arm

open VG.Arm
open VG.Impl.Sha512.Arm (ld st add64)
open VG.Impl.Blake2.Arm.B (xor64 rotr rotr')

/-- `++`, grouping to the right (see `Impl/Sha512/Arm.lean`). -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `t2 :=` the high half of `x · y` (`x`, `y` 32 bits), from the four products
of their 16-bit halves, each below 2³²: with `t0`, `t1` the low halves, `t2`,
`t3` the high halves and `t4`, the high half is
`x₁y₁ + ⌊x₀y₁ / 2¹⁶⌋ + ⌊x₁y₀ / 2¹⁶⌋ + ⌊(⌊x₀y₀ / 2¹⁶⌋ + x₀y₁ mod 2¹⁶ + x₁y₀ mod 2¹⁶) / 2¹⁶⌋`.
`x` and `y` are kept; `t0`–`t4` are written. -/
def mulHi (x y t0 t1 t2 t3 t4 : Reg) : List Instr :=
  [.mov t0 (.shifted x .lsl 16), .mov t0 (.shifted t0 .lsr 16),
   .mov t1 (.shifted y .lsl 16), .mov t1 (.shifted t1 .lsr 16),
   .mov t2 (.shifted y .lsr 16), .mov t3 (.shifted x .lsr 16),
   .mul t4 t0 t1, .mul t0 t0 t2, .mul t1 t3 t1, .mul t2 t3 t2,
   .mov t3 (.shifted t0 .lsl 16), .mov t3 (.shifted t3 .lsr 16),
   .dp .add t3 t3 (.shifted t4 .lsr 16),
   .mov t4 (.shifted t1 .lsl 16), .dp .add t3 t3 (.shifted t4 .lsr 16),
   .dp .add t2 t2 (.shifted t0 .lsr 16), .dp .add t2 t2 (.shifted t1 .lsr 16),
   .dp .add t2 t2 (.shifted t3 .lsr 16)]

/-- `(al, ah) := addMul((al, ah), (bl, bh))`: the product of the low halves
(`t0` low, `t2` high), doubled, then `b` added. -/
def addMul (al ah bl bh t0 t1 t2 t3 t4 : Reg) : List Instr :=
  mulHi al bl t0 t1 t2 t3 t4 +++ .mul t0 al bl :: add64 t0 t2 t0 t2 +++ add64 al ah t0 t2 +++
    add64 al ah bl bh

/-- GB (RFC 9106 §3.6) on the words at `[r3, #a]`, …, `[r3, #d]`, with the
registers of BLAKE2b's `G` (`Impl/Blake2/Arm/CompressB.lean`). -/
def gb (a b c d : Nat) : List Instr :=
  ld .r4 .r5 .r3 a +++ ld .r6 .r7 .r3 b +++ ld .r8 .r9 .r3 c +++ ld .r10 .r11 .r3 d +++
  -- a := addMul(a, b)
  addMul .r4 .r5 .r6 .r7 .r0 .r1 .r2 .r12 .lr +++
  -- d := (d ⊕ a) >>> 32: in (r11, r10)
  xor64 .r10 .r11 .r4 .r5 +++
  -- c := addMul(c, d)
  addMul .r8 .r9 .r11 .r10 .r0 .r1 .r2 .r12 .lr +++
  -- b := (b ⊕ c) >>> 24: in (r12, r7)
  xor64 .r6 .r7 .r8 .r9 +++ rotr 24 .r12 .r6 .r7 +++
  -- a := addMul(a, b)
  addMul .r4 .r5 .r12 .r7 .r0 .r1 .r2 .r6 .lr +++
  -- d := (d ⊕ a) >>> 16: in (r6, r10)
  xor64 .r11 .r10 .r4 .r5 +++ rotr 16 .r6 .r11 .r10 +++
  -- c := addMul(c, d)
  addMul .r8 .r9 .r6 .r10 .r0 .r1 .r2 .r11 .lr +++
  -- b := (b ⊕ c) >>> 63: in (r11, r7)
  xor64 .r12 .r7 .r8 .r9 +++ rotr' 63 .r11 .r12 .r7 +++
  st .r4 .r5 .r3 a +++ st .r11 .r7 .r3 b +++ st .r8 .r9 .r3 c +++ st .r6 .r10 .r3 d

/-- The word `k` of the permuted block. -/
def wOff (k : Nat) : Nat := 1024 + 8 * k

/-- GB on words `a, b, c, d` of the permuted block. -/
def gbAt (a b c d : Nat) : Prog isa := .block (gb (wOff a) (wOff b) (wOff c) (wOff d))

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  let step (a b c d : Fin 16) := gbAt (index a).val (index b).val (index c).val (index d).val
  .seq (step 0 4 8 12) <| .seq (step 1 5 9 13) <|
  .seq (step 2 6 10 14) <| .seq (step 3 7 11 15) <|
  .seq (step 0 5 10 15) <| .seq (step 1 6 11 12) <|
  .seq (step 2 7 8 13) (step 3 4 9 14)

/-- The rows, then the columns. -/
def rounds : Prog isa :=
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block []))

/-- Where the caller's registers and `out` are kept. -/
def saved : List (Reg × Nat) :=
  [(.r4, 2048), (.r5, 2052), (.r6, 2056), (.r7, 2060), (.r8, 2064), (.r9, 2068), (.r10, 2072),
   (.r11, 2076), (.lr, 2080)]

def outOff : Nat := 2084

/-- What the prologue stores: the caller's registers and `out`. -/
def spill : List (Reg × Nat) := saved ++ [(.r2, outOff)]

/-- Save the caller's registers and `out`. -/
def prologue : List Instr := spill.map fun p => .str p.1 .r3 p.2

/-- 32-bit word `i` of X XOR Y, to both halves of scratch. -/
def initWord (i : Nat) : List Instr :=
  [.ldr .r4 .r0 (4 * i), .ldr .r5 .r1 (4 * i), .dp .eor .r4 .r4 (.reg .r5),
    .str .r4 .r3 (4 * i), .str .r4 .r3 (1024 + 4 * i)]

/-- 32-bit word `i` of the output: the permuted block XOR R, to `out` (`r2`). -/
def finishWord (i : Nat) : List Instr :=
  [.ldr .r4 .r3 (1024 + 4 * i), .ldr .r5 .r3 (4 * i), .dp .eor .r4 .r4 (.reg .r5),
    .str .r4 .r2 (4 * i)]

/-- Load `out`, write the output, and restore the caller's registers. -/
def epilogue : List Instr :=
  .ldr .r2 .r3 outOff :: (List.range 256).flatMap finishWord +++
    saved.map (fun p => .ldr p.1 .r3 p.2)

def compress : Prog isa :=
  .seq (.block (prologue +++ (List.range 256).flatMap initWord)) (.seq rounds (.block epilogue))

end VG.Impl.Argon2.Arm
