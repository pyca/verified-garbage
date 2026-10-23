module

public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SM3 compression function: PPC64LE implementation

`vg_sm3_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the AArch64 implementation (`Impl/Sm3/AArch64.lean`):
* The registers `A … H` live in the low words of `r7`–`r12`, `r14` and
  `r15`; the unrolled iterations rename them: `A … D` rotate through
  `group₁`, `E … H` through `group₂`, and in iteration `j`, register `k` is in
  `var j k`. The additions act on all 64 bits, so the high words hold
  carries, which the word rotations (`rotrwi`, which reads the low word) and
  the stores ignore.
* The message expansion is a 16-word window in `scratch[0..64)`: iteration
  `j` computes `W_{j+4}` (from the block while `j + 4 < 16`, loaded
  big-endian with `lwbrx`, indexed by `r0`), then reads `W_j` and `W_{j+4}`.
* `r14`–`r19` are nonvolatile: they are saved in `scratch[64..112)` first and
  restored last.
* `r3`–`r6` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm3.PPC64LE

open VG.PPC64LE

/-- The registers holding `A … D`. -/
def group₁ : List Reg := [.r7, .r8, .r9, .r10]

/-- The registers holding `E … H`. -/
def group₂ : List Reg := [.r11, .r12, .r14, .r15]

/-- The register holding register `k` (`A = 0, …, H = 7`) at the start of
iteration `j`. -/
def var (j k : Nat) : Reg :=
  if k < 4 then group₁.getD ((k + 4 - j % 4) % 4) .r7
  else group₂.getD ((k + 4 - j % 4) % 4) .r7

/-- Temporaries. -/
def T0 : Reg := .r16
def T1 : Reg := .r17
def T2 : Reg := .r18
def T3 : Reg := .r19

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19].getD i .r14

/-- Save them in `scratch[64..112)`. -/
def save : List Instr := (List.range 6).flatMap fun i => [.store .d (saved i) .r6 (64 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 6).flatMap fun i => [.load .d (saved i) .r6 (64 + 8 * i)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Compute `W_i` into its slot:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`
for `i ≥ 16`, word `i` of the block (big-endian) before. -/
def expand (i : Nat) : List Instr :=
  if i < 16 then [
    .li .r0 (4 * i),
    .loadRev .w T0 .r4 .r0,
    .store .w T0 .r6 (slot i)]
  else [
    -- T0 := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
    .load .w T0 .r6 (slot i),
    .load .w T1 .r6 (slot (i + 7)),
    .logic .xor T0 T0 T1,
    .load .w T1 .r6 (slot (i + 13)),
    .rotr .w T1 T1 17,
    .logic .xor T0 T0 T1,
    -- T0 := P_1(T0)
    .rotr .w T1 T0 17,
    .rotr .w T2 T0 9,
    .logic .xor T0 T0 T1,
    .logic .xor T0 T0 T2,
    -- T0 := T0 xor (W_{i-13} <<< 7) xor W_{i-6}
    .load .w T1 .r6 (slot (i + 3)),
    .rotr .w T1 T1 25,
    .logic .xor T0 T0 T1,
    .load .w T1 .r6 (slot (i + 10)),
    .logic .xor T0 T0 T1,
    .store .w T0 .r6 (slot i)]

/-- `T_j <<< (j mod 32)`, an immediate. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  let a := var j 0; let b := var j 1; let c := var j 2; let d := var j 3
  let e := var j 4; let f := var j 5; let g := var j 6; let h := var j 7
  [ -- T0 := A <<< 12; T1 := SS1 = ((A <<< 12) + E + (T_j <<< j)) <<< 7
    .rotr .w T0 a 20,
    .add T1 T0 e,
    .lis T2 ((tj j).extractLsb' 16 16),
    .ori T2 T2 ((tj j).extractLsb' 0 16),
    .add T1 T1 T2,
    .rotr .w T1 T1 25,
    -- h := H + SS1
    .add h h T1,
    -- d := D + SS2, SS2 = SS1 xor (A <<< 12)
    .logic .xor T0 T0 T1,
    .add d d T0,
    -- h := h + W_j; d := d + W'_j, W'_j = W_j xor W_{j+4}
    .load .w T2 .r6 (slot j),
    .add h h T2,
    .load .w T3 .r6 (slot (j + 4)),
    .logic .xor T3 T2 T3,
    .add d d T3] ++
  -- d := d + FF_j(A, B, C), which is TT1
  (if j < 16 then [
    .logic .xor T0 a b,
    .logic .xor T0 T0 c]
   else [
    -- (A or B) and C or (A and B)
    .logic .or T0 a b,
    .logic .and T0 T0 c,
    .logic .and T1 a b,
    .logic .or T0 T0 T1] : List Instr) ++
  [.add d d T0] ++
  -- h := h + GG_j(E, F, G), which is TT2
  (if j < 16 then [
    .logic .xor T0 e f,
    .logic .xor T0 T0 g]
   else [
    -- (F xor G) and E xor G
    .logic .xor T0 f g,
    .logic .and T0 T0 e,
    .logic .xor T0 T0 g] : List Instr) ++
  [ .add h h T0,
    -- C' := B <<< 9; G' := F <<< 19
    .rotr .w b b 23,
    .rotr .w f f 13,
    -- h := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17)
    .rotr .w T0 h 23,
    .rotr .w T1 h 15,
    .logic .xor h h T0,
    .logic .xor h h T1]

/-- `W_0 … W_3`, then iterations `0 … n-1`, each computing `W_{j+4}` first. -/
def rounds : Nat → Prog isa
  | 0 => .block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)
  | n + 1 => .seq (rounds n) (.block (expand (n + 4) ++ round n))

/-- Load the hash value (`64 % 4 = 0`, so the registers are in the same
places after the 64 iterations). -/
def load : List Instr := (List.range 8).map fun k => .load .w (var 0 k) .r3 (4 * k)

/-- `V_{i+1} = (A || … || H) xor V_i` (loading all of `V_i` before storing
any of it). -/
def update : List Instr :=
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * k)) ++
  (List.range 4).map (fun k => .logic .xor (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .logic .xor (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .store .w (var 0 k) .r3 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 64, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sm3.PPC64LE
