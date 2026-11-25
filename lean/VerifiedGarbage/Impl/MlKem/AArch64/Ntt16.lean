module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
public import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: the parts of the NTT in 16-bit lanes

The NTTs of `Ntt16/` compute on eight coefficients at a time, in the 16-bit
lanes of AdvSIMD registers, as signed integers.

A product by a constant `z`, `|z| < q / 2`, is
`x · z - t · q` with `t = sqrdmulh(x, quo z)`, `quo z = round(2¹⁵ z / q)`.
For every 16-bit `x`, `t` is so close to `x · z / q` that the result, which is
computed modulo `2¹⁶`, is less than `q` in absolute value: a butterfly needs no
bound on what it multiplies, and adds less than `q` to what it does not.

The least residue of `x`, `|x| ≤ 8q`, is `x - ⌊t / 2¹¹⌋ · q` with
`t = sqrdmulh(x, 20159)` and `20159 = round(2²⁶ / q)`: the rounding of
`sqrdmulh` adds a little less than `2⁻¹² < 1 / q` to the quotient, more than
the constant's error takes away from it, so that the floor is exactly that of
`x / q` (`canon`).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

open VG.AArch64 VG.Impl.MlKem.AArch64

/-! ## Constants -/

/-- `ζ_k`. -/
def zeta (k : Nat) : Nat := zetaTable.getD k 0

/-- The halfword of the residue of `z < q` between `-q / 2` and `q / 2`. -/
def cen (z : Nat) : Nat := if 3329 < 2 * z then z + 65536 - 3329 else z

/-- The halfword of `round(2¹⁵ c / q)`, `c` that residue. -/
def quo (z : Nat) : Nat :=
  let t := (z * 2 ^ 16 + 3329) / 6658
  if 3329 < 2 * z then t + 2 ^ 15 else t

/-- The two halfwords of a multiplication by `z`. -/
def pair (z : Nat) : List Nat := [cen z, quo z]

/-- The doublewords of rows of halfwords. -/
def rowWords : List Nat → List (BitVec 64)
  | a :: b :: c :: d :: l => BitVec.ofNat 64 (a + 2 ^ 16 * b + 2 ^ 32 * c + 2 ^ 48 * d) :: rowWords l
  | _ => []

/-! ## Instructions -/

/-- `v<n>`. -/
def V (n : Nat) : VReg :=
  [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
    .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30,
    .v31].getD n .v0

/-- The multiplier of a product: lane `i` of a register, or a whole one. -/
inductive Mul
  | lane (r : VReg) (i : Nat)
  | all (r : VReg)

/-- A multiplication of the lanes of `n` by a multiplier. -/
def mulBy (op : VMulHOp) (d n : VReg) : Mul → Instr
  | .lane r i => .vop (.mulHE op d n r i)
  | .all r => .vop (.mulH op d n r)

/-- Halfword `i` of the rows in the registers from `v<b>`. -/
def at_ (b i : Nat) : Mul := .lane (V (b + i / 8)) (i % 8)

/-- `q`, in the first lane of `v0`. -/
def qLane : Mul := .lane .v0 0

/-- Row `i` of the table at `x2`. -/
def row (d : VReg) (i : Nat) : Instr := .ldrq d .x2 (16 * i)

/-- The vector of coefficients `8 i, …, 8 i + 7`. -/
def ldv (d : VReg) (i : Nat) : Instr := .ldrq d .x0 (16 * i)
def stv (d : VReg) (i : Nat) : Instr := .strq d .x0 (16 * i)

/-- `n` turns of streams run together: in each, the next instruction of each of the streams `run`,
to which the first of those that `wait` is added every `d` turns, `k` turns from now. -/
def turns (d : Nat) : Nat → Nat → List (List Instr) → List (List Instr) → List Instr
  | 0, _, _, _ => []
  | n + 1, 0, run, s :: wait =>
    (run ++ [s]).filterMap List.head? ++ turns d n (d - 1) ((run ++ [s]).map List.tail) wait
  | n + 1, k, run, wait => run.filterMap List.head? ++ turns d n (k - 1) (run.map List.tail) wait

/-- Instruction streams of at most `3 d` instructions run together, each starting `d` turns after the
one before. -/
def stagger (d : Nat) (ss : List (List Instr)) : List Instr :=
  turns d (d * (ss.length + 2)) 0 [] ss

/-- `q` and 20159, and the multipliers by `ζ₁, …, ζ₇`: two rows. -/
def headRows : List Nat := [3329, 20159] ++ (List.range 7).flatMap fun k => pair (zeta (k + 1))

/-- A row of copies of `q` and 20159. -/
def qRow : List Nat := (List.range 4).flatMap fun _ => [3329, 20159]

/-- The index of the upper input of butterfly `n` of a layer of sixteen vectors whose lower
inputs are `d` further. -/
def upper (d n : Nat) : Nat := n / d * (2 * d) + n % d

end VG.Impl.MlKem.AArch64.Ntt16
