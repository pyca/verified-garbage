import VerifiedGarbage.Spec.Sm3
import VerifiedGarbage.TCB.Arm.Isa

/-!
# SM3 compression function: ARMv7 implementation

`vg_sm3_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

The same structure as the x86-64 implementation, with fewer registers:
* The registers `A … H` live in `r4`–`r11`; the unrolled iterations rename
  them: `A … D` rotate through `group₁`, `E … H` through `group₂`, and in
  iteration `j`, register `k` is in `var j k`. The temporaries are `r12` and
  `lr`; rotations are shifted operands, so `A <<< 12` is recomputed rather
  than kept.
* The message expansion is a 16-word window in `scratch[0..64)`: iteration
  `j` computes `W_{j+4}` (from the block while `j + 4 < 16`), then reads `W_j`
  and `W_{j+4}`.
* `r4`–`r11` and `lr` are saved in `scratch[64..100)` and restored on exit.
* `r0`–`r3` (the pointers and the block count) are public; no address and no
  branch depends on anything else.
-/

namespace VG.Impl.Sm3.Arm

open VG.Arm

/-- The registers holding `A … D`. -/
def group₁ : List Reg := [.r4, .r5, .r6, .r7]

/-- The registers holding `E … H`. -/
def group₂ : List Reg := [.r8, .r9, .r10, .r11]

/-- The register holding register `k` (`A = 0, …, H = 7`) at the start of
iteration `j`. -/
def var (j k : Nat) : Reg :=
  if k < 4 then group₁.getD ((k + 4 - j % 4) % 4) .r4
  else group₂.getD ((k + 4 - j % 4) % 4) .r4

/-- Temporaries. -/
def T1 : Reg := .r12
def T2 : Reg := .lr

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Compute `W_i` into its slot:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`
for `i ≥ 16`, word `i` of the block (big-endian) before. -/
def expand (i : Nat) : List Instr :=
  if i < 16 then [
    .ldr T1 .r1 (4 * i),
    .rev T1 T1,
    .str T1 .r3 (slot i)]
  else [
    -- T1 := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
    .ldr T1 .r3 (slot i),
    .ldr T2 .r3 (slot (i + 7)),
    .dp .eor T1 T1 (.reg T2),
    .ldr T2 .r3 (slot (i + 13)),
    .dp .eor T1 T1 (.shifted T2 .ror 17),
    -- T1 := P_1(T1)
    .dp .eor T2 T1 (.shifted T1 .ror 17),
    .dp .eor T1 T2 (.shifted T1 .ror 9),
    -- T1 := T1 xor (W_{i-13} <<< 7) xor W_{i-6}
    .ldr T2 .r3 (slot (i + 3)),
    .dp .eor T1 T1 (.shifted T2 .ror 25),
    .ldr T2 .r3 (slot (i + 10)),
    .dp .eor T1 T1 (.reg T2),
    .str T1 .r3 (slot i)]

/-- `T_j <<< (j mod 32)`, an immediate. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  let a := var j 0; let b := var j 1; let c := var j 2; let d := var j 3
  let e := var j 4; let f := var j 5; let g := var j 6; let h := var j 7
  [ -- T1 := SS1 = ((A <<< 12) + E + (T_j <<< j)) <<< 7
    .mov T1 (.shifted a .ror 20),
    .dp .add T1 T1 (.reg e),
    .movw T2 ((tj j).extractLsb' 0 16),
    .movt T2 ((tj j).extractLsb' 16 16),
    .dp .add T1 T1 (.reg T2),
    .mov T1 (.shifted T1 .ror 25),
    -- h := H + SS1
    .dp .add h h (.reg T1),
    -- d := D + SS2, SS2 = SS1 xor (A <<< 12)
    .dp .eor T1 T1 (.shifted a .ror 20),
    .dp .add d d (.reg T1),
    -- h := h + W_j; d := d + W'_j, W'_j = W_j xor W_{j+4}
    .ldr T1 .r3 (slot j),
    .dp .add h h (.reg T1),
    .ldr T2 .r3 (slot (j + 4)),
    .dp .eor T1 T1 (.reg T2),
    .dp .add d d (.reg T1)] ++
  -- d := d + FF_j(A, B, C), which is TT1
  (if j < 16 then [
    .dp .eor T1 a (.reg b),
    .dp .eor T1 T1 (.reg c)]
   else [
    -- (A or B) and C or (A and B)
    .dp .orr T1 a (.reg b),
    .dp .and T1 T1 (.reg c),
    .dp .and T2 a (.reg b),
    .dp .orr T1 T1 (.reg T2)] : List Instr) ++
  [.dp .add d d (.reg T1)] ++
  -- h := h + GG_j(E, F, G), which is TT2
  (if j < 16 then [
    .dp .eor T1 e (.reg f),
    .dp .eor T1 T1 (.reg g)]
   else [
    -- (F xor G) and E xor G
    .dp .eor T1 f (.reg g),
    .dp .and T1 T1 (.reg e),
    .dp .eor T1 T1 (.reg g)] : List Instr) ++
  [ .dp .add h h (.reg T1),
    -- C' := B <<< 9; G' := F <<< 19
    .mov b (.shifted b .ror 23),
    .mov f (.shifted f .ror 13),
    -- h := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17)
    .dp .eor T1 h (.shifted h .ror 23),
    .dp .eor h T1 (.shifted h .ror 15)]

/-- `W_0 … W_3`, then iterations `0 … n-1`, each computing `W_{j+4}` first. -/
def rounds : Nat → Prog isa
  | 0 => .block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)
  | n + 1 => .seq (rounds n) (.block (expand (n + 4) ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 64), (.r5, 68), (.r6, 72), (.r7, 76), (.r8, 80), (.r9, 84), (.r10, 88), (.r11, 92),
   (.lr, 96)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the hash value (`64 % 4 = 0`, so the registers are in the same
places after the 64 iterations). -/
def load : List Instr := (List.range 8).map fun k => .ldr (var 0 k) .r0 (4 * k)

/-- `V_{i+1} = (A || … || H) xor V_i`. -/
def update : List Instr :=
  (List.range 8).flatMap fun k => [
    .ldr T1 .r0 (4 * k),
    .dp .eor (var 0 k) (var 0 k) (.reg T1),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [.dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sm3.Arm
