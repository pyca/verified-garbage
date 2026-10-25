module

public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# SM3 compression function: RISC-V implementation

`vg_sm3_compress(state = a0, blocks = a1, n = a2, scratch = a3)`.

The structure of the PPC64LE implementation (`Impl/Sm3/PPC64LE.lean`), for
RV64I, which has neither rotates nor byte-reversed loads, and faults on
misaligned accesses, with the idioms and the use of `scratch` of SHA-256's
RISC-V implementation (`Impl/Sha256/RISCV64.lean`):
* The registers `A … H` live in the low words of `t0`–`t6` and `a4`; the
  unrolled iterations rename them: `A … D` rotate through `group₁`, `E … H`
  through `group₂`, and in iteration `j`, register `k` is in `var j k`. The
  additions act on all 64 bits, so the high words hold carries and the sign
  extensions of the `*w` shifts, which the word shifts and the stores
  ignore.
* A rotation left by `n` is `slliw` by `n` and `srliw` by `32 - n`,
  combined by `or`.
* The hash value (`state`, an array of `u32`) and the blocks are argument
  buffers, whose alignment the contract does not state, so they are read
  and written a byte at a time (`Impl/Words/RISCV64.lean`); the words of a
  block are big-endian.
* `scratch` is rounded up to a multiple of 8 (it has room to spare), so the
  16-word message expansion window in its first 64 bytes, and `s0`, the one
  callee-saved register used, saved at offset 64, take naturally aligned
  word and doubleword accesses. Iteration `j` computes `W_{j+4}` (from the
  block while `j + 4 < 16`), then reads `W_j` and `W_{j+4}`.
* `a0`–`a3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm3.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64

/-- The registers holding `A … D`. -/
def group₁ : List Reg := [.t0, .t1, .t2, .t3]

/-- The registers holding `E … H`. -/
def group₂ : List Reg := [.t4, .t5, .t6, .a4]

/-- The register holding register `k` (`A = 0, …, H = 7`) at the start of
iteration `j`. -/
def var (j k : Nat) : Reg :=
  if k < 4 then group₁.getD ((k + 4 - j % 4) % 4) .t0
  else group₂.getD ((k + 4 - j % 4) % 4) .t0

/-- Temporaries. -/
def T0 : Reg := .a5
def T1 : Reg := .a6
def T2 : Reg := .a7
def T3 : Reg := .s0

/-- Round `scratch` up to a multiple of 8, and save `s0` in it. -/
def save : List Instr := [.addi .a3 .a3 7, .logicImm .and .a3 .a3 (-8), .store .d .s0 .a3 64]

/-- Restore `s0`. -/
def restore : List Instr := [.load .d .s0 .a3 64]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- `d := x <<< n` for a word `x`, with `tmp` clobbered (`0 < n < 32`; `d` may be `x`). -/
def rotl (d tmp x : Reg) (n : Nat) : List Instr :=
  [.shift .sll .w tmp x n, .shift .srl .w d x (32 - n), .logic .or d d tmp]

/-- Compute `W_i` into its slot:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`
for `i ≥ 16`, word `i` of the block (big-endian) before. -/
def expand (i : Nat) : List Instr :=
  if i < 16 then loadBE32 T0 T1 .a1 (4 * i) ++ [.store .w T0 .a3 (slot i)]
  else
    -- T0 := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
    [.load .w T0 .a3 (slot i), .load .w T1 .a3 (slot (i + 7)), .logic .xor T0 T0 T1,
      .load .w T1 .a3 (slot (i + 13))] ++ rotl T1 T2 T1 15 ++ [.logic .xor T0 T0 T1] ++
    -- T0 := P_1(T0)
    rotl T1 T2 T0 15 ++ rotl T2 T3 T0 23 ++ [.logic .xor T0 T0 T1, .logic .xor T0 T0 T2] ++
    -- T0 := T0 xor (W_{i-13} <<< 7) xor W_{i-6}
    [.load .w T1 .a3 (slot (i + 3))] ++ rotl T1 T2 T1 7 ++
    [.logic .xor T0 T0 T1, .load .w T1 .a3 (slot (i + 10)), .logic .xor T0 T0 T1,
      .store .w T0 .a3 (slot i)]

/-- `T_j <<< (j mod 32)`, a constant. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  let a := var j 0; let b := var j 1; let c := var j 2; let d := var j 3
  let e := var j 4; let f := var j 5; let g := var j 6; let h := var j 7
  -- T0 := A <<< 12; T1 := SS1 = ((A <<< 12) + E + (T_j <<< j)) <<< 7
  rotl T0 T1 a 12 ++ [.add T1 T0 e] ++ li32 T2 (tj j) ++ [.add T1 T1 T2] ++ rotl T1 T2 T1 7 ++
  [ -- h := H + SS1
    .add h h T1,
    -- d := D + SS2, SS2 = SS1 xor (A <<< 12)
    .logic .xor T0 T0 T1,
    .add d d T0,
    -- h := h + W_j; d := d + W'_j, W'_j = W_j xor W_{j+4}
    .load .w T2 .a3 (slot j),
    .add h h T2,
    .load .w T3 .a3 (slot (j + 4)),
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
  [.add h h T0] ++
  -- C' := B <<< 9; G' := F <<< 19
  rotl b T0 b 9 ++ rotl f T0 f 19 ++
  -- h := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17)
  rotl T0 T1 h 9 ++ rotl T1 T2 h 17 ++ [.logic .xor h h T0, .logic .xor h h T1]

/-- `W_0 … W_3`, then iterations `0 … n-1`, each computing `W_{j+4}` first. -/
def rounds : Nat → Prog isa
  | 0 => .block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)
  | n + 1 => .seq (rounds n) (.block (expand (n + 4) ++ round n))

/-- Load the hash value (`64 % 4 = 0`, so the registers are in the same
places after the 64 iterations). -/
def load : List Instr := (List.range 8).flatMap fun k => loadLE32 (var 0 k) T0 .a0 (4 * k)

/-- `V_{i+1} = (A || … || H) xor V_i`, a word at a time, stored. -/
def updateW (k : Nat) : List Instr :=
  loadLE32 T0 T1 .a0 (4 * k) ++ [.logic .xor (var 0 k) (var 0 k) T0] ++
    storeLE32 (var 0 k) T0 .a0 (4 * k)

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .a1 .a1 64, .addi .a2 .a2 (-1)]

/-- One block. -/
def body : Prog isa :=
  .seq (.block load) (.seq (rounds 64) (.block ((List.range 8).flatMap updateW ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .a2) (.block []) (.loop body (.nonzero .a2))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sm3.RISCV64
