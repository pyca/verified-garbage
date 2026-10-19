module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: the NTT in 16-bit lanes

The NTT of Algorithm 9 on eight coefficients at a time, in the 16-bit lanes
of AdvSIMD registers, as signed integers.

* A product `a · z mod q`, for `|a| < 2¹⁵` and a zeta `z < q`, is
  `r = a · z - t · q` with `t = sqrdmulh(a, z')`, `z' = round(z · 2¹⁵ / q)`
  (`tw`): `t` is `a · z / q` within `1/2 + |a| / 2¹⁶ < 1`, so `|r| < q`, and
  `r` is computed modulo `2¹⁶` (`mul`, `mls`). A butterfly adds and subtracts
  it, so after `k` layers every lane is less than `(k + 1) q` in absolute
  value; after the seven, `8q < 2¹⁵`, and no layer reduces.
* Pass 1 (`pass1Body`, four times): the layers with `len = 128, 64, 32` on
  the eight coefficients `32r + 8c + i` (`i < 8`) of each row `r < 8`, for
  the chunk `c`, read from `f` (`u32`s, narrowed by `uzp1`) and written to
  `scratch` as 16-bit lanes. Their zetas `ζ₁ … ζ₇` and their `tw` are in the
  lanes of `v18` and `v19`.
* Pass 2 (`pass2Body`, eight times): the layers with `len = 16, 8, 4, 2` on
  the 32 coefficients of block `b` (four vectors), the last two after
  gathering the pairs of each butterfly into two vectors (`trn1`, `trn2`);
  then each lane reduced to less than `q` in absolute value (the product
  by 1, `tw 1 = 10`), made nonnegative (`q` added to a negative lane), and
  widened back to `u32`s in `f` (`zip1`, `zip2` with zero).
* The zetas of pass 2 are stored in `scratch` at 512 first (`blockTable`):
  for block `b`, `Zs = (ζ_{8+b}, ζ_{16+2b}, ζ_{17+2b}, 0, ζ_{32+4b} … ζ_{35+4b})`,
  its `tw`, `Z₇ = (ζ_{64+8b} … ζ_{71+8b})` and its `tw`; the lanes each
  butterfly needs are spread by `dup` (element), `zip1` and `zip2`.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

open VG.AArch64 VG.Impl.MlKem.AArch64

/-- `round(z · 2¹⁵ / q)`, for `z < q`. -/
def tw (z : Nat) : Nat := (z * 2 ^ 16 + 3329) / (2 * 3329)

/-- `ζ_k`. -/
def zeta (k : Nat) : Nat := zetaTable.getD k 0

/-- The 32 halfwords of block `b`'s zetas: `Zs`, its `tw`, `Z₇`, its `tw`. -/
def blockHalves (b : Nat) : List Nat :=
  let zs := [zeta (8 + b), zeta (16 + 2 * b), zeta (17 + 2 * b), 0] ++
    (List.range 4).map fun j => zeta (32 + 4 * b + j)
  let z7 := (List.range 8).map fun j => zeta (64 + 8 * b + j)
  zs ++ zs.map tw ++ z7 ++ z7.map tw

/-- The 256 halfwords of the table of pass 2. -/
def tableHalves : List Nat := (List.range 8).flatMap blockHalves

/-- The halfwords `H` at `[r + off]`, four at a time through `x9`. -/
def halves (H : List Nat) (r : Reg) (off : Nat) : List Instr :=
  (List.range (H.length / 4)).flatMap fun g =>
    [.movz .x .x9 (BitVec.ofNat 16 (H.getD (4 * g) 0)) 0,
     .movk .x .x9 (BitVec.ofNat 16 (H.getD (4 * g + 1) 0)) 1,
     .movk .x .x9 (BitVec.ofNat 16 (H.getD (4 * g + 2) 0)) 2,
     .movk .x .x9 (BitVec.ofNat 16 (H.getD (4 * g + 3) 0)) 3,
     .str .x .x9 r (off + 8 * g)]

/-- `q` in the lanes of `v31`, `tw 1 = 10` in those of `v30`, zero in `v29`;
`ζ₁ … ζ₇` in lanes 0–6 of `v18` and their `tw` in those of `v19`. -/
def consts : List Instr :=
  [.movz .x .x9 3329 0, .vop (.dup .h8 .v31 .x9), .movz .x .x9 10 0, .vop (.dup .h8 .v30 .x9),
    .vop (.movi0 .v29)] ++
  (List.range 7).flatMap fun k =>
    [.movz .x .x9 (BitVec.ofNat 16 (zeta (k + 1))) 0, .vop (.ins .h8 .v18 k .x9),
     .movz .x .x9 (BitVec.ofNat 16 (tw (zeta (k + 1)))) 0, .vop (.ins .h8 .v19 k .x9)]

/-- The butterflies on the lanes of `x` and `y` with the zetas `z` and their
`tw` in `t`: `x ← x + r`, `y ← x - r`, `r = y · z mod q` (in `v16`). -/
def bf (x y z t : VReg) : List Instr :=
  [.vop (.mulH .mul .v16 y z), .vop (.mulH .sqrdmulh .v17 y t), .vop (.mulH .mls .v16 .v17 .v31),
    .vop (.sub .h8 y x .v16), .vop (.add .h8 x x .v16)]

/-- The rows' registers. -/
def row (r : Nat) : VReg := [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7].getD r .v0

/-- Butterflies on the rows `a`, `b` with lane `k` of `v18`, `v19`. -/
def bfRows (k : Nat) (ps : List (Nat × Nat)) : List Instr :=
  [.vop (.dupE .h8 .v22 .v18 k), .vop (.dupE .h8 .v23 .v19 k)] ++
    ps.flatMap fun (a, b) => bf (row a) (row b) .v22 .v23

/-- The first three layers on the rows of a chunk. -/
def pass1Arith : List Instr :=
  bfRows 0 [(0, 4), (1, 5), (2, 6), (3, 7)] ++
  bfRows 1 [(0, 2), (1, 3)] ++ bfRows 2 [(4, 6), (5, 7)] ++
  bfRows 3 [(0, 1)] ++ bfRows 4 [(2, 3)] ++ bfRows 5 [(4, 5)] ++ bfRows 6 [(6, 7)]

/-- Chunk `c`: `x2 = f + 32c`, `x3 = scratch + 16c`. -/
def pass1Body : List Instr :=
  ((List.range 8).flatMap fun r =>
    [.ldrq .v20 .x2 (128 * r), .ldrq .v21 .x2 (128 * r + 16),
     .vop (.perm .uzp1 .h8 (row r) .v20 .v21)]) ++
  pass1Arith ++
  ((List.range 8).map fun r => .strq (row r) .x3 (64 * r)) ++
  [.addImm .x .x2 .x2 32, .addImm .x .x3 .x3 16, .subImm .x .x5 .x5 1]

/-- Chunk `c` of `f` with 16-bit coefficients: `x2 = f + 16c`, `x3 = scratch + 16c`. -/
def pass1BodyW : List Instr :=
  ((List.range 8).map fun r => .ldrq (row r) .x2 (64 * r)) ++
  pass1Arith ++
  ((List.range 8).map fun r => .strq (row r) .x3 (64 * r)) ++
  [.addImm .x .x2 .x2 16, .addImm .x .x3 .x3 16, .subImm .x .x5 .x5 1]

/-- Layers 6 and 7 on the vectors `p`, `q'` (coefficients `8i … 8i + 15` of
the block), with the zetas of layer 6 in `z6`, `t6` and of layer 7 in `z7`,
`t7`, through `v4`, `v5`. -/
def lastTwo (p q' z6 t6 z7 t7 : VReg) : List Instr :=
  [.vop (.perm .trn1 .d2 .v4 p q'), .vop (.perm .trn2 .d2 .v5 p q')] ++ bf .v4 .v5 z6 t6 ++
  [.vop (.perm .trn1 .s4 p .v4 .v5), .vop (.perm .trn2 .s4 q' .v4 .v5)] ++ bf p q' z7 t7 ++
  [.vop (.perm .trn1 .s4 .v4 p q'), .vop (.perm .trn2 .s4 .v5 p q'),
   .vop (.perm .trn1 .d2 p .v4 .v5), .vop (.perm .trn2 .d2 q' .v4 .v5)]

/-- `x` reduced to `[0, q)`, from less than `2¹⁵` in absolute value. -/
def normalize (x : VReg) : List Instr :=
  [.vop (.mulH .sqrdmulh .v16 x .v30), .vop (.mulH .mls x .v16 .v31),
   .vop (.shift .sshr .h8 .v16 x 15), .vop (.logic .and .v16 .v16 .v31), .vop (.add .h8 x x .v16)]

/-- The four layers of a block of pass 2, and each lane reduced. -/
def pass2Arith : List Instr :=
  [.vop (.dupE .h8 .v24 .v20 0), .vop (.dupE .h8 .v25 .v21 0)] ++
  bf .v0 .v2 .v24 .v25 ++ bf .v1 .v3 .v24 .v25 ++
  [.vop (.dupE .h8 .v24 .v20 1), .vop (.dupE .h8 .v25 .v21 1)] ++ bf .v0 .v1 .v24 .v25 ++
  [.vop (.dupE .h8 .v24 .v20 2), .vop (.dupE .h8 .v25 .v21 2)] ++ bf .v2 .v3 .v24 .v25 ++
  [.vop (.perm .zip2 .h8 .v24 .v20 .v20), .vop (.perm .zip2 .h8 .v25 .v21 .v21),
   .vop (.perm .zip1 .s4 .v26 .v24 .v24), .vop (.perm .zip1 .s4 .v27 .v25 .v25),
   .vop (.perm .zip1 .h8 .v28 .v22 .v22), .vop (.perm .zip1 .h8 .v19 .v23 .v23)] ++
  lastTwo .v0 .v1 .v26 .v27 .v28 .v19 ++
  [.vop (.perm .zip2 .s4 .v26 .v24 .v24), .vop (.perm .zip2 .s4 .v27 .v25 .v25),
   .vop (.perm .zip2 .h8 .v28 .v22 .v22), .vop (.perm .zip2 .h8 .v19 .v23 .v23)] ++
  lastTwo .v2 .v3 .v26 .v27 .v28 .v19 ++
  ([VReg.v0, .v1, .v2, .v3].flatMap normalize)

/-- The loads of block `b`. -/
def pass2Loads : List Instr :=
  [.ldrq .v0 .x2 0, .ldrq .v1 .x2 16, .ldrq .v2 .x2 32, .ldrq .v3 .x2 48,
   .ldrq .v20 .x6 0, .ldrq .v21 .x6 16, .ldrq .v22 .x6 32, .ldrq .v23 .x6 48]

/-- Block `b`: `x2 = scratch + 64b`, `x6 = scratch + 512 + 64b`, `x4 = f + 128b`. -/
def pass2Body : List Instr :=
  pass2Loads ++ pass2Arith ++
  ((List.range 4).flatMap fun i =>
    [.vop (.perm .zip1 .h8 .v24 (row i) .v29), .vop (.perm .zip2 .h8 .v25 (row i) .v29),
     .strq .v24 .x4 (32 * i), .strq .v25 .x4 (32 * i + 16)]) ++
  [.addImm .x .x2 .x2 64, .addImm .x .x6 .x6 64, .addImm .x .x4 .x4 128, .subImm .x .x5 .x5 1]

/-- Block `b` of `f` with 16-bit coefficients: `x4 = f + 64b`. -/
def pass2BodyW : List Instr :=
  pass2Loads ++ pass2Arith ++
  ((List.range 4).map fun i => .strq (row i) .x4 (16 * i)) ++
  [.addImm .x .x2 .x2 64, .addImm .x .x6 .x6 64, .addImm .x .x4 .x4 64, .subImm .x .x5 .x5 1]

def ntt : Prog isa :=
  .seq (.block (halves tableHalves .x1 512 ++ consts ++
    ([mov .x2 .x0, .addImm .x .x3 .x1 0, .movz .x .x5 4 0] : List Instr))) <|
  .seq (.loop (.block pass1Body) (.nonzero .x .x5)) <|
  .seq (.block [.addImm .x .x2 .x1 0, .addImm .x .x6 .x1 512, mov .x4 .x0, .movz .x .x5 8 0])
    (.loop (.block pass2Body) (.nonzero .x .x5))

/-! ## `nttInv` -/

/-- The 32 halfwords of block `b`'s zetas for the inverse: `Zs = (ζ_{15-b},
ζ_{31-2b}, ζ_{30-2b}, 0, ζ_{63-4b} … ζ_{60-4b})`, its `tw`,
`Z₇ = (ζ_{127-8b} … ζ_{120-8b})`, its `tw`. -/
def invBlockHalves (b : Nat) : List Nat :=
  let zs := [zeta (15 - b), zeta (31 - 2 * b), zeta (30 - 2 * b), 0] ++
    (List.range 4).map fun j => zeta (63 - 4 * b - j)
  let z7 := (List.range 8).map fun j => zeta (127 - 8 * b - j)
  zs ++ zs.map tw ++ z7 ++ z7.map tw

def invTableHalves : List Nat := (List.range 8).flatMap invBlockHalves

/-- `q` in the lanes of `v31`, 10 in those of `v30`, zero in `v29`. -/
def qConsts : List Instr :=
  [.movz .x .x9 3329 0, .vop (.dup .h8 .v31 .x9), .movz .x .x9 10 0, .vop (.dup .h8 .v30 .x9),
    .vop (.movi0 .v29)]

/-- `ζ₇, ζ₆, ζ₅, ζ₄, ζ₃, ζ₂, ζ₁, 3303` in the lanes of `v18` and their `tw` in
those of `v19`. -/
def invConsts : List Instr :=
  (List.range 8).flatMap fun k =>
    let z := if k < 7 then zeta (7 - k) else 3303
    [.movz .x .x9 (BitVec.ofNat 16 z) 0, .vop (.ins .h8 .v18 k .x9),
     .movz .x .x9 (BitVec.ofNat 16 (tw z)) 0, .vop (.ins .h8 .v19 k .x9)]

/-- The inverse butterflies on the lanes of `x` and `y`: `x ← x + y`,
`y ← (y - x) · z mod q`. -/
def gs (x y z t : VReg) : List Instr :=
  [.vop (.sub .h8 .v17 y x), .vop (.add .h8 x x y), .vop (.mulH .mul y .v17 z),
    .vop (.mulH .sqrdmulh .v17 .v17 t), .vop (.mulH .mls y .v17 .v31)]

/-- Lanes reduced to less than `q` in absolute value, from less than `2¹⁵`. -/
def reduce (x : VReg) : List Instr :=
  [.vop (.mulH .sqrdmulh .v16 x .v30), .vop (.mulH .mls x .v16 .v31)]

/-- Inverse butterflies on the rows `a`, `b` with lane `k` of `v18`, `v19`. -/
def gsRows (k : Nat) (ps : List (Nat × Nat)) : List Instr :=
  [.vop (.dupE .h8 .v22 .v18 k), .vop (.dupE .h8 .v23 .v19 k)] ++
    ps.flatMap fun (a, b) => gs (row a) (row b) .v22 .v23

/-- The layers with `len = 2, 4` on the vectors `p`, `q'`. -/
def firstTwo (p q' z7 t7 z6 t6 : VReg) : List Instr :=
  [.vop (.perm .trn1 .d2 .v4 p q'), .vop (.perm .trn2 .d2 .v5 p q'),
   .vop (.perm .trn1 .s4 p .v4 .v5), .vop (.perm .trn2 .s4 q' .v4 .v5)] ++ gs p q' z7 t7 ++
  [.vop (.perm .trn1 .s4 .v4 p q'), .vop (.perm .trn2 .s4 .v5 p q')] ++ gs .v4 .v5 z6 t6 ++
  [.vop (.perm .trn1 .d2 p .v4 .v5), .vop (.perm .trn2 .d2 q' .v4 .v5)]

/-- The table of block `b` and its first four layers of the inverse. -/
def invPass1Arith : List Instr :=
  [.ldrq .v20 .x6 0, .ldrq .v21 .x6 16, .ldrq .v22 .x6 32, .ldrq .v23 .x6 48,
   .vop (.perm .zip2 .h8 .v24 .v20 .v20), .vop (.perm .zip2 .h8 .v25 .v21 .v21),
   .vop (.perm .zip1 .h8 .v28 .v22 .v22), .vop (.perm .zip1 .h8 .v19 .v23 .v23),
   .vop (.perm .zip1 .s4 .v26 .v24 .v24), .vop (.perm .zip1 .s4 .v27 .v25 .v25)] ++
  firstTwo .v0 .v1 .v28 .v19 .v26 .v27 ++
  [.vop (.perm .zip2 .h8 .v28 .v22 .v22), .vop (.perm .zip2 .h8 .v19 .v23 .v23),
   .vop (.perm .zip2 .s4 .v26 .v24 .v24), .vop (.perm .zip2 .s4 .v27 .v25 .v25)] ++
  firstTwo .v2 .v3 .v28 .v19 .v26 .v27 ++
  [.vop (.dupE .h8 .v24 .v20 1), .vop (.dupE .h8 .v25 .v21 1)] ++ gs .v0 .v1 .v24 .v25 ++
  [.vop (.dupE .h8 .v24 .v20 2), .vop (.dupE .h8 .v25 .v21 2)] ++ gs .v2 .v3 .v24 .v25 ++
  ([VReg.v0, .v1, .v2, .v3].flatMap reduce) ++
  [.vop (.dupE .h8 .v24 .v20 0), .vop (.dupE .h8 .v25 .v21 0)] ++
  gs .v0 .v2 .v24 .v25 ++ gs .v1 .v3 .v24 .v25

/-- Block `b`: `x2 = f + 128b`, `x3 = scratch + 64b`, `x6 = scratch + 512 + 64b`. -/
def invPass1Body : List Instr :=
  ((List.range 4).flatMap fun i =>
    [.ldrq .v20 .x2 (32 * i), .ldrq .v21 .x2 (32 * i + 16),
     .vop (.perm .uzp1 .h8 (row i) .v20 .v21)]) ++
  invPass1Arith ++
  ((List.range 4).map fun i => .strq (row i) .x3 (16 * i)) ++
  [.addImm .x .x2 .x2 128, .addImm .x .x3 .x3 64, .addImm .x .x6 .x6 64, .subImm .x .x5 .x5 1]

/-- Block `b` of `f` with 16-bit coefficients: `x2 = f + 64b`. -/
def invPass1BodyW : List Instr :=
  ((List.range 4).map fun i => .ldrq (row i) .x2 (16 * i)) ++
  invPass1Arith ++
  ((List.range 4).map fun i => .strq (row i) .x3 (16 * i)) ++
  [.addImm .x .x2 .x2 64, .addImm .x .x3 .x3 64, .addImm .x .x6 .x6 64, .subImm .x .x5 .x5 1]

/-- The last three layers of the inverse on the rows of a chunk, and the factor 3303 and its
`tw` in `v22`, `v23`. -/
def invPass2Arith : List Instr :=
  gsRows 0 [(0, 1)] ++ gsRows 1 [(2, 3)] ++ gsRows 2 [(4, 5)] ++ gsRows 3 [(6, 7)] ++
  gsRows 4 [(0, 2), (1, 3)] ++ gsRows 5 [(4, 6), (5, 7)] ++
  ((List.range 8).flatMap fun r => reduce (row r)) ++
  gsRows 6 [(0, 4), (1, 5), (2, 6), (3, 7)] ++
  [.vop (.dupE .h8 .v22 .v18 7), .vop (.dupE .h8 .v23 .v19 7)]

/-- Chunk `c`: `x2 = scratch + 16c`, `x3 = f + 32c`; the zetas `ζ₇ … ζ₁` and
3303 in `v18`, `v19` (built after pass 1, which uses `v19`). -/
def invPass2Body : List Instr :=
  ((List.range 8).map fun r => .ldrq (row r) .x2 (64 * r)) ++
  invPass2Arith ++
  ((List.range 8).flatMap fun r =>
    [.vop (.mulH .mul .v16 (row r) .v22), .vop (.mulH .sqrdmulh .v17 (row r) .v23),
     .vop (.mulH .mls .v16 .v17 .v31), .vop (.shift .sshr .h8 .v17 .v16 15),
     .vop (.logic .and .v17 .v17 .v31), .vop (.add .h8 .v16 .v16 .v17),
     .vop (.perm .zip1 .h8 .v24 .v16 .v29), .vop (.perm .zip2 .h8 .v25 .v16 .v29),
     .strq .v24 .x3 (128 * r), .strq .v25 .x3 (128 * r + 16)]) ++
  [.addImm .x .x2 .x2 16, .addImm .x .x3 .x3 32, .subImm .x .x5 .x5 1]

/-- Chunk `c` of `f` with 16-bit coefficients: `x3 = f + 16c`. -/
def invPass2BodyW : List Instr :=
  ((List.range 8).map fun r => .ldrq (row r) .x2 (64 * r)) ++
  invPass2Arith ++
  ((List.range 8).flatMap fun r =>
    [.vop (.mulH .mul .v16 (row r) .v22), .vop (.mulH .sqrdmulh .v17 (row r) .v23),
     .vop (.mulH .mls .v16 .v17 .v31), .vop (.shift .sshr .h8 .v17 .v16 15),
     .vop (.logic .and .v17 .v17 .v31), .vop (.add .h8 .v16 .v16 .v17),
     .strq .v16 .x3 (64 * r)]) ++
  [.addImm .x .x2 .x2 16, .addImm .x .x3 .x3 16, .subImm .x .x5 .x5 1]

def nttInv : Prog isa :=
  .seq (.block (halves invTableHalves .x1 512 ++ qConsts ++
    ([mov .x2 .x0, .addImm .x .x3 .x1 0, .addImm .x .x6 .x1 512, .movz .x .x5 8 0] : List Instr))) <|
  .seq (.loop (.block invPass1Body) (.nonzero .x .x5)) <|
  .seq (.block (invConsts ++ [.addImm .x .x2 .x1 0, mov .x3 .x0, .movz .x .x5 4 0]))
    (.loop (.block invPass2Body) (.nonzero .x .x5))

end VG.Impl.MlKem.AArch64.Ntt16
