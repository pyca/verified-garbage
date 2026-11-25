module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16

/-!
# ML-KEM on AArch64: the inverse NTT of 16-bit coefficients

`code` is `NTT⁻¹` (Algorithm 10) of the polynomial at `x0`, in place.

Its first three layers (`len = 2, 4, 8`) run on one block of sixteen coefficients, two vectors, at
a time (`block`); the others on the sixteen even vectors of eight coefficients, then on the sixteen
odd ones (`column`), with `len` a distance of 1, 2, 4 and 8 registers.

Coefficients are not reduced before the fourth layer, whose sums and differences are all multiplied
by `128⁻¹` (the differences by it times their zeta), which is both the scaling that ends
Algorithm 10 and the only reduction of the sums. The first two lanes of the even vectors, sums of
eight inputs, are up to `8q` then: `8q` is subtracted from their sums, which may wrap around, so
that they are in range again. The three other layers add up to eight products, less than `8q`. The
last one's sums are brought to their least residues by `sqrdmulh` and a shift, as in the NTT, and
its differences, products between `-q` and `q`, by adding `q` to the negative ones.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16.Inverse

open VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- The name of the table. -/
def name : String := "VG_MLKEM16_INTT_ZETAS"

/-- `128⁻¹ mod q`. -/
def scale : Nat := 3303

/-- The four rows of block `b`'s first two layers: the multipliers of the layer with `len = 2`, then
those of the layer with `len = 4`. -/
def blockRows (b : Nat) : List Nat :=
  let z7 := (List.range 8).map fun i => zeta (127 - 4 * b - i / 2)
  let z6 := (List.range 8).map fun i => zeta (63 - 2 * b - i / 4)
  z7.map cen ++ z7.map quo ++ z6.map cen ++ z6.map quo

/-- What is subtracted from the lanes of the even vectors' sums in the fourth layer. -/
def offsets : List Nat := [26632, 26632, 0, 0, 0, 0, 0, 0]

/-- The 76 rows of the table: those of the blocks' last layer, `qRow`, the columns' five, the offsets,
`q`, and the blocks' own. -/
def rows : List Nat :=
  ((List.range 16).flatMap fun b => pair (zeta (31 - b))) ++ qRow ++
    headRows ++ ((List.range 8).flatMap fun k => pair (zeta (8 + k) * scale % 3329)) ++
    (List.range 4).flatMap (fun _ => pair scale) ++ offsets ++ List.replicate 8 3329 ++
    (List.range 16).flatMap blockRows

/-- The doublewords of the table. -/
def words : List (BitVec 64) := rowWords rows

/-- `u ← u + v` and `d ← z (v - u)`, with the temporary `h` and `q` in the lane `q`. -/
def butterfly (u v d h : VReg) (z t q : Mul) : List Instr :=
  [.vop (.sub .h8 d v u), .vop (.add .h8 u u v),
    mulBy .sqrdmulh h d t, mulBy .mul d d z, mulBy .mls d h q]

/-- As `butterfly`, with multipliers loaded from the rows `i` and `i + 1` of the table into `z`
and `t`. -/
def rowButterfly (u v d h z t : VReg) (i : Nat) : List Instr :=
  [row z i, row t (i + 1)] ++ butterfly u v d h (.all z) (.all t) (.lane .v6 0)

/-- The first three layers of block `b`. -/
def block (A B C D z t : VReg) (b : Nat) : List Instr :=
  [ldv A (2 * b), ldv B (2 * b + 1),
    .vop (.perm .uzp1 .s4 C A B), .vop (.perm .uzp2 .s4 D A B)] ++
    rowButterfly C D A B z t (12 + 4 * b) ++
    [.vop (.perm .trn1 .s4 B C A), .vop (.perm .trn2 .s4 D C A)] ++
    rowButterfly B D A C z t (14 + 4 * b) ++
    [.vop (.perm .trn1 .d2 C B A), .vop (.perm .trn2 .d2 D B A)] ++
    butterfly C D A B (at_ 0 (2 * b)) (at_ 0 (2 * b + 1)) (.lane .v6 0) ++
    [stv C (2 * b), stv A (2 * b + 1)]

/-- Register `i` of the six of block `b`'s turn. -/
def turnReg (b i : Nat) : VReg :=
  let r := 6 * (b % 3) + i
  if r < 16 then V (16 + r) else V (r - 12)

/-- Block `b`, in the registers of its turn. -/
def turn (b : Nat) : List Instr :=
  block (turnReg b 0) (turnReg b 1) (turnReg b 2) (turnReg b 3) (turnReg b 4) (turnReg b 5) b

/-- The registers of butterfly `n` of the layer with `len = 16 d`. -/
def up (d n : Nat) : VReg := V (16 + upper d n)
def lo (d n : Nat) : VReg := V (16 + upper d n + d)

/-- The fourth layer, whose outputs are multiplied by `128⁻¹` too: of the even vectors if `even`. -/
def scaleLayer (even : Bool) : List Instr :=
  (List.range 8).flatMap fun n =>
    let u := up 1 n
    let v := lo 1 n
    [.vop (.sub .h8 .v5 v u), .vop (.add .h8 u u v)] ++
      (if even then [.vop (.sub .h8 u u .v7)] else []) ++
      [mulBy .sqrdmulh .v6 .v5 (at_ 2 (2 * (7 - n) + 1)), mulBy .mul v .v5 (at_ 2 (2 * (7 - n))),
        mulBy .mls v .v6 qLane,
        mulBy .sqrdmulh .v6 u (.lane .v4 1), mulBy .mul u u (.lane .v4 0), mulBy .mls u .v6 qLane]

/-- `u ← u + v` and `v ← z (v - u)`, `z` being `ζ_k`. -/
def columnButterfly (u v : VReg) (k : Nat) : List Instr :=
  [.vop (.sub .h8 .v5 v u), .vop (.add .h8 u u v),
    mulBy .sqrdmulh .v6 .v5 (at_ 0 (2 * k + 1)), mulBy .mul v .v5 (at_ 0 (2 * k)), mulBy .mls v .v6 qLane]

/-- The layers with `len = 32` and `64` (`d = 2` and `4`). -/
def columnLayer (d : Nat) : List Instr :=
  (List.range 8).flatMap fun n => columnButterfly (up d n) (lo d n) (16 / d - 1 - n / d)

/-- The last layer, with `q` in the lanes of `v7`. -/
def lastLayer : List Instr :=
  (List.range 8).flatMap fun n =>
    let u := up 8 n
    let v := lo 8 n
    columnButterfly u v 1 ++
      [.vop (.mulHE .sqrdmulh .v6 u .v0 1), .vop (.shift .sshr .h8 .v6 .v6 11), mulBy .mls u .v6 qLane,
        .vop (.shift .sshr .h8 .v6 v 15), .vop (.logic .and .v6 .v6 .v7), .vop (.add .h8 v v .v6)]

/-- The last four layers of the vectors `j, j + 2, …, j + 30`. -/
def column (j : Nat) : List Instr :=
  ((List.range 16).map fun i => ldv (V (16 + i)) (2 * i + j)) ++
    (if j = 0 then [row .v7 10] else []) ++
    scaleLayer (j = 0) ++ columnLayer 2 ++ columnLayer 4 ++ [row .v7 11] ++ lastLayer ++
    (List.range 16).map fun i => stv (V (16 + i)) (2 * i + j)

def body : List Instr :=
  [row .v0 0, row .v1 1, row .v2 2, row .v3 3, row .v6 4] ++ stagger 12 ((List.range 16).map turn) ++
    [row .v0 5, row .v1 6, row .v2 7, row .v3 8, row .v4 9] ++ column 0 ++ column 1

/-- The function `vg_mlkem16_inv_ntt`. -/
def code : Prog isa := .block (.adrSym .x2 name :: body)

end VG.Impl.MlKem.AArch64.Ntt16.Inverse
