module

public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SM3 compression with the AArch64 SM3 instructions

`vg_sm3_compress_sm4(state = x0, blocks = x1, n = x2, scratch = x3)`, for
CPUs with FEAT_SM3 (which Rust names `sm4`, with FEAT_SM4): the contract of
`vg_sm3_compress`, whose `scratch` it does not use.

* The registers `A … D` are the four lanes of `v5` and `E … H` those of `v6`,
  `A` and `E` in lane 3, as the SM3 instructions take them: the hash value is
  loaded once, before the first block, and the four words of each half are
  reversed (`rev64 .4s` swaps the words of each doubleword, `ext #8` the
  doublewords); it is reversed back and stored once, after the last block.
  Each block copies the hash value it starts from to `v21` and `v22`, for the
  feed-forward.
* The message words `W₄ₖ … W₄ₖ₊₃` are the lanes of `msg k`, one of `v0`–`v4`:
  group `n` of four iterations reads `msg n` and `msg (n + 1)`, and, while a
  later group needs them, first computes the words of `msg (n + 4)` (the
  register of `msg (n - 1)`, which no later group reads) with SM3PARTW1 and
  SM3PARTW2. `v16` holds `W'₄ₙ … W'₄ₙ₊₃`.
* `T_j <<< (j mod 32)` is lane 3 of `v17` in the even iterations and of
  `v18` in the odd ones, rotated left by one in each iteration (`shl #1`,
  then `sri #31`); `T₀` is set at the start of the block and `T₁₆ <<< 16` at
  iteration 16, from `w4`.
* Iteration `j`: SM3SS1 makes `SS1` in lane 3 of `v7`, SM3TT1A (SM3TT1B from
  iteration 16) the new `A … D`, SM3TT2A (SM3TT2B) the new `E … H`.

Only caller-saved registers are used (`x4`, `v0`–`v7`, `v16`–`v22`), and no
stack. `x0`–`x2` (the pointers and the block count) and `x4` (a constant) are
public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm3.AArch64.Sm4

open VG.AArch64

/-- The register holding the message words `4 k` through `4 k + 3`. -/
def msg (k : Nat) : VReg := [.v0, .v1, .v2, .v3, .v4].getD (k % 5) .v0

/-- The register holding `T_j <<< (j mod 32)` in iteration `j`. -/
def treg (j : Nat) : VReg := if j % 2 = 0 then .v17 else .v18

/-- `T_j <<< (j mod 32)` -/
def tRot (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Set every lane of `v17` to `c`. -/
def tset (c : BitVec 32) : List Instr :=
  [.movz .w .x4 (c.extractLsb' 0 16) 0, .movk .w .x4 (c.extractLsb' 16 16) 1,
   .vop (.dup .s4 .v17 .x4)]

/-- Before group `n`: the constant of its first iteration, where it is not the
one before it rotated. -/
def tinit (n : Nat) : List Instr := if n = 0 ∨ n = 4 then tset (tRot (4 * n)) else []

/-- Before group `n`: the message words of group `n + 4`, if a group reads
them (`W₆₇` is the last, of `W'₆₃`). -/
def expand (n : Nat) : List Instr :=
  if n ≤ 12 then
    [.vop (.ext (msg (n + 4)) (msg (n + 1)) (msg (n + 2)) 12),
     .vop (.ext .v19 (msg n) (msg (n + 1)) 12),
     .vop (.ext .v20 (msg (n + 2)) (msg (n + 3)) 8),
     .vop (.sm3partw1 (msg (n + 4)) (msg n) (msg (n + 3))),
     .vop (.sm3partw2 (msg (n + 4)) .v20 .v19)]
  else []

/-- SM3TT1A, or SM3TT1B if `b` (from iteration 16). -/
def tt1 (b : Bool) : Sm3TtOp := if b then .tt1b else .tt1a

/-- SM3TT2A, or SM3TT2B if `b` (from iteration 16). -/
def tt2 (b : Bool) : Sm3TtOp := if b then .tt2b else .tt2a

/-- Iteration `j`. -/
def round (j : Nat) : List Instr :=
  [.vop (.sm3ss1 .v7 .v5 (treg j) .v6),
   .vop (.shift .shl .s4 (treg (j + 1)) (treg j) 1),
   .vop (.shift .sri .s4 (treg (j + 1)) (treg j) 31),
   .vop (.sm3tt (tt1 (decide (16 ≤ j))) .v5 .v7 .v16 (j % 4)),
   .vop (.sm3tt (tt2 (decide (16 ≤ j))) .v6 .v7 (msg (j / 4)) (j % 4))]

/-- `W'₄ₙ … W'₄ₙ₊₃` -/
def wprime (n : Nat) : List Instr := [.vop (.logic .eor .v16 (msg n) (msg (n + 1)))]

/-- Group `n`: iterations `4 n` through `4 n + 3`. -/
def group (n : Nat) : List Instr :=
  tinit n ++ (expand n ++ (wprime n ++
    (round (4 * n) ++ (round (4 * n + 1) ++ (round (4 * n + 2) ++ round (4 * n + 3))))))

/-- The first `n` groups. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (group n))

/-- Reverse the four words of `v5` and of `v6`. -/
def wordRev : List Instr :=
  [.vop (.rev .rev64s .v5 .v5), .vop (.ext .v5 .v5 .v5 8),
   .vop (.rev .rev64s .v6 .v6), .vop (.ext .v6 .v6 .v6 8)]

/-- Load the hash value. -/
def load : List Instr := [.ldrq .v5 .x0 0, .ldrq .v6 .x0 16]

/-- Load a block's sixteen words, and copy the hash value. -/
def fetch : List Instr :=
  [.ldrq .v0 .x1 0, .ldrq .v1 .x1 16, .ldrq .v2 .x1 32, .ldrq .v3 .x1 48,
   .vop (.rev .rev32b .v0 .v0), .vop (.rev .rev32b .v1 .v1),
   .vop (.rev .rev32b .v2 .v2), .vop (.rev .rev32b .v3 .v3),
   .vop (.mov .v21 .v5), .vop (.mov .v22 .v6)]

/-- The feed-forward, and the next block. -/
def fold : List Instr :=
  [.vop (.logic .eor .v5 .v5 .v21), .vop (.logic .eor .v6 .v6 .v22),
   .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- Store the hash value, after the last block. -/
def store : List Instr := [.strq .v5 .x0 0, .strq .v6 .x0 16]

/-- One block. -/
def body : Prog isa := .seq (.block fetch) (.seq (rounds 16) (.block fold))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block (load ++ wordRev)) (.seq (.loop body (.nonzero .x .x2)) (.block (wordRev ++ store))))

end VG.Impl.Sm3.AArch64.Sm4
