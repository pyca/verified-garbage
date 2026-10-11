module

public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-!
# Short Weierstrass curves on AArch64: a fixed-base comb

`[k]P` for a fixed point `P` and a scalar `k < 2^(4J)` whose bits are a table
of bytes (byte `t` is bit `t`, as `bits` writes it), from `J` tables of
constants: table `j` holds `[m 16^j]P` for `m = 1 … 8`, affine and in
Montgomery form. With the nibbles `k_j` of `k` and the digits
`d_j = k_j - 8 ∈ [-8, 7]`, `k = c + Σ d_j 16^j` for `c = 8 Σ_{j<J} 16^j`, so

  `[k]P = [c]P + Σ_j [d_j 16^j]P`:

the accumulator `A` starts at `[c]P` (a constant), and iteration `j` adds the
entry of table `j` for `|d_j|` (or the point at infinity for `d_j = 0`),
negated if `d_j < 0`, by the complete addition for `a = -3` (`rcb3`, with `b` in
`S.b3`), for `j = J - 1` down to `0`:
`J` additions, and no doublings.

The digits are secret, so their entries are selected in constant time. The
masks of the magnitudes `0 … 8` (all ones exactly for `|d_j|`) are in
registers (`maskReg`); every word of every entry is built from immediates
and ANDed with its mask, and the words are ORed together (`selectWord`).
The entry's `Z` is `1` (Montgomery's, `R mod p`) unless the magnitude is
zero, when the entry is `(0 : 1 : 0)`. The negation computes `0 - y` and
selects it by the mask of the digit's sign. The table's code is chosen by
the iteration's counter `x19`, which is public, as are every address and
branch.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

/-! ## Digits, shared with the window method -/

/-- The registers holding the masks of the magnitudes `0 … 8`. -/
def maskRegs : List Reg := [.x1, .x3, .x5, .x6, .x7, .x8, .x10, .x11, .x12]

/-- The mask of magnitude `m`. -/
def maskReg (m : Nat) : Reg := maskRegs.getD m .x1

/-- `x2` = the nibble `j = x19` of the scalar: `b₀ + 2b₁ + 4b₂ + 8b₃` of the
bytes at `x0 + 4 x19 + bits`, by Horner's rule, through `x16` and `x4`. -/
def nibble (bits : Nat) : List Instr :=
  [.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16,
    .ldrb .x2 .x16 (bits + 3), .add .x .x2 .x2 .x2, .ldrb .x4 .x16 (bits + 2),
    .add .x .x2 .x2 .x4, .add .x .x2 .x2 .x2, .ldrb .x4 .x16 (bits + 1),
    .add .x .x2 .x2 .x4, .add .x .x2 .x2 .x2, .ldrb .x4 .x16 bits, .add .x .x2 .x2 .x4]

/-- From the nibble `k` in `x2`: `|k - 8|` into `x2`, through `x3`, `x4` and `x9`:
`x3 = k - 8`, `x4` all ones if it is negative, and `|k - 8| = (x3 ^ x4) - x4`. -/
def magnitude : List Instr :=
  [.subImm .x .x3 .x2 8, .lsr .x .x4 .x3 63, .movz .x .x9 0 0, .sub .x .x4 .x9 .x4,
    .logic .eor .x .x2 .x3 .x4, .sub .x .x2 .x2 .x4]

/-- The masks of the magnitudes from `|d|` in `x2` (at most 8): first
`maskReg m = [|d| < m]` for `m = 1 … 8`, then `maskReg 0 = -[|d| < 1]`,
`maskReg m = [|d| < m] - [|d| < m + 1]` for `m = 1 … 7` and
`maskReg 8 = [|d| < 8] - 1`: all ones exactly for `m = |d|`. -/
def masks : List Instr :=
  (((List.range 8).flatMap fun i =>
    [.subImm .x (maskReg (i + 1)) .x2 (i + 1), .lsr .x (maskReg (i + 1)) (maskReg (i + 1)) 63]) : List Instr) ++
  ([.sub .x (maskReg 0) .x9 (maskReg 1)] : List Instr) ++
  (((List.range 7).map fun i => .sub .x (maskReg (i + 1)) (maskReg (i + 1)) (maskReg (i + 2))) : List Instr) ++
  ([.subImm .x (maskReg 8) (maskReg 8) 1] : List Instr)

/-- The digit's masks: its nibble, its magnitude and the masks. -/
def digit (bits : Nat) : List Instr := nibble bits ++ magnitude ++ masks

/-- `x3` all ones if digit `x19` is negative, that is if bit 3 of its nibble is
clear: `x3 = b₃ - 1`, through `x16`. -/
def signMask (bits : Nat) : List Instr :=
  [.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16, .ldrb .x3 .x16 (bits + 3), .subImm .x .x3 .x3 1]

/-- `[y] = -[y]` (through `[neg]`, with zero at `z`) if digit `x19` of the
table at `bits` is negative. -/
def negY (M : Mod) (neg z y bits : Nat) : List Instr :=
  Mont.AArch64.sub M neg z y ++ signMask bits ++ sel M.n y y neg

/-- `[o] = [a]`, a point. -/
def copyPt (n : Nat) (o a : Pt) : List Instr := copy n o.x a.x ++ copy n o.y a.y ++ copy n o.z a.z

namespace CombCfg

variable (K : CombCfg)

/-- `x4 |= v & mask m` for the word `v`, built in `x9`, through `x2`. -/
def selectCand (v : BitVec 64) (m : Nat) : List Instr :=
  const64 .x9 v ++ [.logic .and .x .x2 .x9 (maskReg m), .logic .orr .x .x4 .x4 .x2]

/-- Word `w` of the coordinate whose values for the magnitudes `1 … 8` are
`vs` and, for magnitude `0`, `z`, into `[o + 8w]`: built in `x4`. -/
def selectWord (z : Nat) (vs : List Nat) (o w : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (if z = 0 then [] else selectCand (wordOf z w) 0) ++
    ((List.range 8).flatMap fun i => selectCand (wordOf (vs.getD i 0) w) (i + 1)) ++
    [st .x4 (o + 8 * w)]

/-- Word `w` of `Z`: `R mod p`'s, unless the magnitude is zero, into `[o + 8w]`. -/
def selectZ (o w : Nat) : List Instr :=
  const64 .x9 (wordOf K.one w) ++ [.bicRor .x .x4 .x9 (maskReg 0) 0, st .x4 (o + 8 * w)]

/-- The entry of table `t` for the magnitude whose mask is all ones, into `E`. -/
def select (t : List (Nat × Nat)) : List Instr :=
  (List.range K.M.n).flatMap (selectWord 0 (t.map (·.1)) K.E.x) ++
  (List.range K.M.n).flatMap (selectWord K.one (t.map (·.2)) K.E.y) ++
  (List.range K.M.n).flatMap ((selectZ K) K.E.z)

end CombCfg

end VG.Impl.Weierstrass.AArch64
