module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16

/-!
# ML-KEM on AArch64: the NTT of 16-bit coefficients

`code` is `NTT` (Algorithm 9) of the polynomial at `x0`, in place.

Its first four layers (`len = 128, 64, 32, 16`) run on the sixteen even vectors of eight
coefficients, then on the sixteen odd ones (`column`): `len` is then a distance of 8, 4, 2 and 1
registers. The last three run on one block of sixteen coefficients, two vectors, at a time
(`block`), which two transpositions arrange so that each butterfly is between two registers.
There are no reductions before the end: an input is less than `q`, each layer adds less than `q`,
so the sums are less than `8q` in absolute value, and `canon` brings them to their least residues.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16.Forward

open VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- The name of the table. -/
def name : String := "VG_MLKEM16_NTT_ZETAS"

/-- The four rows of block `b`'s last two layers: the multipliers of the layer with `len = 4`, then
those of the layer with `len = 2`. -/
def blockRows (b : Nat) : List Nat :=
  let z6 := (List.range 8).map fun i => zeta (32 + 2 * b + i / 4)
  let z7 := (List.range 8).map fun i => zeta (64 + 4 * b + i / 2)
  z6.map cen ++ z6.map quo ++ z7.map cen ++ z7.map quo

/-- The 72 rows of the table. -/
def rows : List Nat :=
  headRows ++ ((List.range 24).flatMap fun k => pair (zeta (k + 8))) ++
    (List.range 16).flatMap blockRows

/-- The doublewords of the table. -/
def words : List (BitVec 64) := rowWords rows

/-- `u, v ← u + z v, u - z v`, with the temporaries `h` and `m`: the multiplier's quotient is `t`. -/
def butterfly (u v h m : VReg) (z t : Mul) : List Instr :=
  [mulBy .sqrdmulh h v t, mulBy .mul m v z, mulBy .mls m h qLane,
    .vop (.sub .h8 v u m), .vop (.add .h8 u u m)]

/-- The multiplier of butterfly `n` of layer `l` of a column, and its quotient (`i = 1`). -/
def columnMul (l n i : Nat) : Mul :=
  if l < 3 then at_ 0 (2 * (2 ^ l + n / (8 / 2 ^ l)) + i) else at_ 2 (2 * n + i)

/-- Layer `l` of the column in `v16 … v31`. -/
def columnLayer (l : Nat) : List Instr :=
  (List.range 8).flatMap fun n =>
    let d := 8 / 2 ^ l
    let u := 16 + upper d n
    butterfly (V u) (V (u + d)) .v4 .v5 (columnMul l n 0) (columnMul l n 1)

/-- The first four layers of the vectors `j, j + 2, …, j + 30`. -/
def column (j : Nat) : List Instr :=
  ((List.range 16).map fun i => ldv (V (16 + i)) (2 * i + j)) ++
    (List.range 4).flatMap columnLayer ++
    (List.range 16).map fun i => stv (V (16 + i)) (2 * i + j)

/-- As `butterfly`, with multipliers loaded from the rows `i` and `i + 1` of the table. -/
def rowButterfly (u v h m : VReg) (i : Nat) : List Instr :=
  [row h (i + 1), row m i] ++ butterfly u v h m (.all m) (.all h)

/-- The least residues of `a` and `b`. -/
def canon (a b s t : VReg) : List Instr :=
  [.vop (.mulHE .sqrdmulh s a .v0 1), .vop (.mulHE .sqrdmulh t b .v0 1),
    .vop (.shift .sshr .h8 s s 11), .vop (.shift .sshr .h8 t t 11),
    mulBy .mls a s qLane, mulBy .mls b t qLane]

/-- The last three layers of block `b`, with the registers `A`, `B`, `C`, `D`. -/
def block (A B C D : VReg) (b : Nat) : List Instr :=
  [ldv A (2 * b), ldv B (2 * b + 1)] ++
    butterfly A B C D (at_ 1 (2 * b)) (at_ 1 (2 * b + 1)) ++
    [.vop (.perm .trn1 .d2 C A B), .vop (.perm .trn2 .d2 D A B)] ++
    rowButterfly C D A B (8 + 4 * b) ++
    [.vop (.perm .trn1 .s4 A C D), .vop (.perm .trn2 .s4 B C D)] ++
    rowButterfly A B C D (10 + 4 * b) ++
    canon A B C D ++
    [.vop (.perm .zip1 .s4 C A B), .vop (.perm .zip2 .s4 D A B), stv C (2 * b), stv D (2 * b + 1)]

/-- Block `b`, in the registers of its turn. -/
def turn (b : Nat) : List Instr :=
  let r := 16 + 4 * (b % 4)
  block (V r) (V (r + 1)) (V (r + 2)) (V (r + 3)) b

def body : List Instr :=
  [row .v0 0, row .v1 1, row .v2 2, row .v3 3] ++ column 0 ++ column 1 ++
    [row .v1 4, row .v2 5, row .v3 6, row .v4 7] ++ stagger 12 ((List.range 16).map turn)

/-- The function `vg_mlkem16_ntt`. -/
def code : Prog isa := .block (.adrSym .x2 name :: body)

end VG.Impl.MlKem.AArch64.Ntt16.Forward
