import VerifiedGarbage.Spec.Sm3
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SM3 compression function: AArch64 implementation

`vg_sm3_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

The same structure as the x86-64 implementation:
* The registers `A … H` live in `w4`–`w11`; the unrolled iterations rename
  them: `A … D` rotate through `group₁`, `E … H` through `group₂`, and in
  iteration `j`, register `k` is in `var j k`.
* The message expansion is a 16-word window in `scratch[0..64)`: iteration
  `j` computes `W_{j+4}` (from the block while `j + 4 < 16`), then reads `W_j`
  and `W_{j+4}`.
* Only caller-saved registers are used (`x0`–`x15`), so nothing is saved.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Sm3.AArch64

open VG.AArch64

/-- The registers holding `A … D`. -/
def group₁ : List Reg := [.x4, .x5, .x6, .x7]

/-- The registers holding `E … H`. -/
def group₂ : List Reg := [.x8, .x9, .x10, .x11]

/-- The register holding register `k` (`A = 0, …, H = 7`) at the start of
iteration `j`. -/
def var (j k : Nat) : Reg :=
  if k < 4 then group₁.getD ((k + 4 - j % 4) % 4) .x4
  else group₂.getD ((k + 4 - j % 4) % 4) .x4

/-- Temporaries. -/
def T0 : Reg := .x12
def T1 : Reg := .x13
def T2 : Reg := .x14
def T3 : Reg := .x15

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Compute `W_i` into its slot:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`
for `i ≥ 16`, word `i` of the block (big-endian) before. -/
def expand (i : Nat) : List Instr :=
  if i < 16 then [
    .ldr .w T0 .x1 (4 * i),
    .rev32 T0 T0,
    .str .w T0 .x3 (slot i)]
  else [
    -- T0 := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
    .ldr .w T0 .x3 (slot i),
    .ldr .w T1 .x3 (slot (i + 7)),
    .logic .eor .w T0 T0 T1,
    .ldr .w T1 .x3 (slot (i + 13)),
    .ror .w T1 T1 17,
    .logic .eor .w T0 T0 T1,
    -- T0 := P_1(T0)
    .ror .w T1 T0 17,
    .ror .w T2 T0 9,
    .logic .eor .w T0 T0 T1,
    .logic .eor .w T0 T0 T2,
    -- T0 := T0 xor (W_{i-13} <<< 7) xor W_{i-6}
    .ldr .w T1 .x3 (slot (i + 3)),
    .ror .w T1 T1 25,
    .logic .eor .w T0 T0 T1,
    .ldr .w T1 .x3 (slot (i + 10)),
    .logic .eor .w T0 T0 T1,
    .str .w T0 .x3 (slot i)]

/-- `T_j <<< (j mod 32)`, an immediate. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  let a := var j 0; let b := var j 1; let c := var j 2; let d := var j 3
  let e := var j 4; let f := var j 5; let g := var j 6; let h := var j 7
  [ -- T0 := A <<< 12; T1 := SS1 = ((A <<< 12) + E + (T_j <<< j)) <<< 7
    .ror .w T0 a 20,
    .add .w T1 T0 e,
    .movz .w T2 ((tj j).extractLsb' 0 16) 0,
    .movk .w T2 ((tj j).extractLsb' 16 16) 1,
    .add .w T1 T1 T2,
    .ror .w T1 T1 25,
    -- h := H + SS1
    .add .w h h T1,
    -- d := D + SS2, SS2 = SS1 xor (A <<< 12)
    .logic .eor .w T0 T0 T1,
    .add .w d d T0,
    -- h := h + W_j; d := d + W'_j, W'_j = W_j xor W_{j+4}
    .ldr .w T2 .x3 (slot j),
    .add .w h h T2,
    .ldr .w T3 .x3 (slot (j + 4)),
    .logic .eor .w T3 T2 T3,
    .add .w d d T3] ++
  -- d := d + FF_j(A, B, C), which is TT1
  (if j < 16 then [
    .logic .eor .w T0 a b,
    .logic .eor .w T0 T0 c]
   else [
    -- (A or B) and C or (A and B)
    .logic .orr .w T0 a b,
    .logic .and .w T0 T0 c,
    .logic .and .w T1 a b,
    .logic .orr .w T0 T0 T1] : List Instr) ++
  [.add .w d d T0] ++
  -- h := h + GG_j(E, F, G), which is TT2
  (if j < 16 then [
    .logic .eor .w T0 e f,
    .logic .eor .w T0 T0 g]
   else [
    -- (F xor G) and E xor G
    .logic .eor .w T0 f g,
    .logic .and .w T0 T0 e,
    .logic .eor .w T0 T0 g] : List Instr) ++
  [ .add .w h h T0,
    -- C' := B <<< 9; G' := F <<< 19
    .ror .w b b 23,
    .ror .w f f 13,
    -- h := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17)
    .ror .w T0 h 23,
    .ror .w T1 h 15,
    .logic .eor .w h h T0,
    .logic .eor .w h h T1]

/-- `W_0 … W_3`, then iterations `0 … n-1`, each computing `W_{j+4}` first. -/
def rounds : Nat → Prog isa
  | 0 => .block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)
  | n + 1 => .seq (rounds n) (.block (expand (n + 4) ++ round n))

/-- Load the hash value (`64 % 4 = 0`, so the registers are in the same
places after the 64 iterations). -/
def load : List Instr := (List.range 8).map fun k => .ldr .w (var 0 k) .x0 (4 * k)

/-- `V_{i+1} = (A || … || H) xor V_i` (loading all of `V_i` before storing
any of it). -/
def update : List Instr :=
  (List.range 4).map (fun k => .ldr .w ([T0, T1, T2, T3].getD k T0) .x0 (4 * k)) ++
  (List.range 4).map (fun k => .logic .eor .w (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .ldr .w ([T0, T1, T2, T3].getD k T0) .x0 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .logic .eor .w (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .str .w (var 0 k) .x0 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sm3.AArch64
