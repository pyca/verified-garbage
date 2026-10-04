import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb

/-!
# Short Weierstrass curves on AArch64: a fixed-base comb from tables in memory

`[k]G` for the fixed point `G` and a scalar `k < 2^(w J)` whose bits are a
table of bytes (byte `t` is bit `t`, as `bits` writes it), from `J` tables of
constants in memory (the `static` `tsym`, `Artifact.consts`, whose address
the code forms with `adrSym`): table `j` holds `[m 2^(wj)]G` for `m = 1 … H` (`H = 2^(w-1)`),
affine and in Montgomery form, entry `m` at `16 n (m - 1)` bytes into the
table (`x` then `y`, `n` words each), the tables `16 n H` bytes apart
(`tcombWords`). With the windows `k_j` of `w` bits of `k` and the digits
`d_j = k_j - H ∈ [-H, H)`, `k = c + Σ d_j 2^(wj)` for `c = H Σ_{j<J} 2^(wj)`:
the accumulator `A` starts at `[c]G` (a constant), and iteration `j` adds the
entry of table `j` for `|d_j|` (or the point at infinity for `d_j = 0`),
negated if `d_j < 0`, by the complete addition for `a = -3`, for
`j = J - 1` down to `0`: `J` additions, and no doublings.

The digits are secret, so their entries are selected in constant time: every
word of every entry of the table is loaded, at an address that depends only
on `j` (public), and `csel` keeps it exactly when its entry's index equals the
magnitude, as the carry says (`selEntry`: `eor` with the index, then `subs`
of 1 sets the carry unless they are equal). The entry's `Z` is `1`
(Montgomery's, `R mod p`) unless the magnitude is zero, when the entry is
`(0 : 1 : 0)`. The negation computes `0 - y` and selects it by the mask of the
digit's sign.
-/

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

/-- The words of the tables `tbl` (affine points, below `p`) in Montgomery form
(`R`), `n` words a coordinate, little-endian: table after table, entry after
entry, `x` then `y`. -/
def tcombWords (n R p : Nat) (tbl : List (List (Nat × Nat))) : List (BitVec 64) :=
  tbl.flatMap fun t => t.flatMap fun (x, y) =>
    (List.range n).map (wordOf (x * R % p)) ++ (List.range n).map (wordOf (y * R % p))

/-- What the comb needs: the field, the complete addition's slots, the
accumulator `A`, the selected entry `E`, the sum `D`, a slot for `-y` and one
holding zero, the table of the scalar's bits, the slot holding the tables'
address, the digits' width `w` and number `J`, the start `[c]G` and
`R mod p`, both in Montgomery form. -/
structure TCombCfg where
  M : Mod
  S : RcbSlots
  A : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  /-- The bytes of the table of bits the scalar's bits fill; the code clears
  those up to `w J`. -/
  kbytes : Nat
  tsym : String
  w : Nat
  J : Nat
  start : Nat × Nat
  one : Nat

/-- The bytes of the window, `x2 = Σ_{i<k} b_i 2^i` for the bytes `b_i` at
`x16 + d + i`, by Horner's rule from the top, through `x4`. -/
def hornerBits : Nat → Nat → List Instr
  | _, 0 => [.movz .x .x2 0 0]
  | d, k + 1 => hornerBits (d + 1) k ++ [.add .x .x2 .x2 .x2, .ldrb .x4 .x16 d, .add .x .x2 .x2 .x4]

/-- `x16 = x0 + w x19`, through `x16`. -/
def winIndex (w : Nat) : List Instr :=
  [.movz .x .x16 (BitVec.ofNat 16 w) 0, .mul .x .x16 .x19 .x16, .add .x .x16 .x0 .x16]

/-- From the window `k` in `x2`: `|k - H|` into `x2`, through `x3`, `x4` and `x9`. -/
def magnitudeH (H : Nat) : List Instr :=
  [.subImm .x .x3 .x2 H, .lsr .x .x4 .x3 63, .movz .x .x9 0 0, .sub .x .x4 .x9 .x4,
    .logic .eor .x .x2 .x3 .x4, .sub .x .x2 .x2 .x4]

/-- `x3` all ones if digit `x19` is negative, that is if the top bit of its
window is clear: `x3 = b_{w-1} - 1`, through `x16`. -/
def signMaskW (w bits : Nat) : List Instr :=
  winIndex w ++ [.ldrb .x3 .x16 (bits + w - 1), .subImm .x .x3 .x3 1]

/-- `[y] = -[y]` (through `[neg]`, with zero at `z`) if digit `x19` is negative. -/
def negYW (M : Mod) (w neg z y bits : Nat) : List Instr :=
  Mont.AArch64.sub M neg z y ++ signMaskW w bits ++ sel M.n y y neg

/-- The registers of the selected entry's `x` and `y` (`2n ≤ 8` words). -/
def entryRegs (n : Nat) : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15].take (2 * n)

namespace TCombCfg

variable (K : TCombCfg)

/-- `H = 2^(w-1)`, the entries of a table. -/
def H : Nat := 2 ^ (K.w - 1)

/-- The bytes of a table. -/
def tblBytes : Nat := 16 * K.M.n * K.H

/-- Entry `m` (from 1) of the table at `x16`: `x1 = m`, the carry clear exactly
if `m` is the magnitude in `x2`, and each word kept in its register unless
it is (with `x5 = 1`), through `x3`, `x4` and `x6`. -/
def selEntry (m : Nat) : List Instr :=
  [.add .x .x1 .x1 .x5, .logic .eor .x .x3 .x2 .x1, .subs .x .x4 .x3 .x5] ++
    (List.range (2 * K.M.n)).flatMap fun i =>
      [.ldr .x .x6 .x16 (16 * K.M.n * (m - 1) + 8 * i),
        .csel .x ((entryRegs K.M.n).getD i .x8) ((entryRegs K.M.n).getD i .x8) .x6]

/-- `x16` = table `x19`'s address, from the static `tsym`'s, with `x7 = 0`,
`x5 = 1` and `x1 = 0`, through `x17`. -/
def selSetup : List Instr :=
  [zero7, .adrSym .x16 K.tsym, .movz .x .x17 (BitVec.ofNat 16 K.tblBytes) 0, .mul .x .x17 .x19 .x17,
    .add .x .x16 .x16 .x17, .movz .x .x5 1 0, .movz .x .x1 0 0]

/-- The registers `rs` set to the words of `v`. -/
def setRegs (rs : List Reg) (v : Nat) : List Instr :=
  (List.range rs.length).flatMap fun i => const64 (rs.getD i .x8) (wordOf v i)

/-- `Z` = `R` (the `n` words of `one`) unless the magnitude in `x2` is zero
(with `x5 = 1` and `x7 = 0`), through `x4` and `x6`. -/
def selZ : List Instr :=
  .subs .x .x4 .x2 .x5 :: (List.range K.M.n).flatMap fun i =>
    const64 .x6 (wordOf K.one i) ++ [.csel .x .x6 .x6 .x7, st .x6 (K.E.z + 8 * i)]

/-- The entry of table `x19` for the magnitude in `x2` into `E`: the table's
address into `x16`; `(0, R)` in the registers, then every entry, kept if its
index is the magnitude; `Z = R` unless the magnitude is zero. -/
def select : List Instr :=
  K.selSetup ++ zeros ((entryRegs K.M.n).take K.M.n) ++
  setRegs ((entryRegs K.M.n).drop K.M.n) K.one ++
  (List.range K.H).flatMap (fun m => selEntry K (m + 1)) ++
  stores ((entryRegs K.M.n).take K.M.n) K.E.x ++ stores ((entryRegs K.M.n).drop K.M.n) K.E.y ++
  K.selZ

/-- The digit's magnitude into `x2`: its window and `|k - H|`. -/
def digit : List Instr := winIndex K.w ++ hornerBits K.bits K.w ++ magnitudeH K.H

/-- Iteration `j = x19 - 1` (with `x19` counting down from `J`): the entry,
negated for a negative digit, added to `A`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: K.digit ++ K.select)) <|
  .seq (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)) <|
  .seq (fprogB K.M (rcb3 K.S K.A K.E K.D)) <|
  .block (copyPt K.M.n K.A K.D)

/-- `A = [c]G`, the bytes of the table of bits past the scalar's cleared (to
`w J`, in words), and the counter. -/
def init : List Instr :=
  setConst K.M.n K.A.x K.start.1 ++ setConst K.M.n K.A.y K.start.2 ++
    setConst K.M.n K.A.z K.one ++
    zero7 :: (List.range ((K.w * K.J - K.kbytes + 7) / 8)).map (fun i => st .x7 (K.bits + K.kbytes + 8 * i)) ++
    [.movz .x .x19 (BitVec.ofNat 16 K.J) 0]

/-- `[k]G` into `A`. -/
def comb : Prog isa := .seq (.block K.init) (.loop K.step (.nonzero .x .x19))

end TCombCfg

end VG.Impl.Weierstrass.AArch64
