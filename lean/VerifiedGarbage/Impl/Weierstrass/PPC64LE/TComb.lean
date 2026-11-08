module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Mont.PPC64LE

/-!
# `[k]G` by a fixed-base signed comb, on PPC64LE

32-bit ARM's comb (`Impl/Weierstrass/Arm/TComb.lean`), on the layout of the
ladder by calls of the point functions (`Impl/Weierstrass/PPC64LE/LadderP.lean`):
the scalar's windows of `w` bits `k_j` (`j < J`) give the digits `k_j - H`
(`H = 2^(w-1)`), and `[k]G = S + Σ_j [(k_j - H) 2^(w j)]G` for the start
`S = [H Σ_j 2^(w j)]G` (`Proof/Weierstrass/CombW.lean`). Row `j` of the
read-only table at `tsym` holds `[m 2^(w j)]G` for `m = 1 … H` (entry
`m - 1`: `x`, then `y`, `n` words each, in Montgomery's form), the rows one
after the other (`Impl/Weierstrass/TCombWords.lean`, the other targets').

From `R = S`, for `j` from `J - 1` down to 0 (`r31 = j + 1`, then `j`):

1. the window `k_j`: its bits read from the ladder's table of the scalar's
   bits (one byte each, at `bits`) by Horner's rule, only the real bits of
   the last window (`topBits` of them, when `r31 = J - 1`, the only branch
   but the loops', on the public counter);
2. the digit's magnitude `|k_j - H|` (`magnitude`), and every entry `m` of
   row `j` scanned: its words are or'ed into the point functions' `Q` under
   the mask of `m = |k_j - H|` (`eqMask`), so that `Q` holds entry
   `|k_j - H| - 1` (or zeros), with `Z = 1`; for a magnitude of zero,
   `Q = (0 : 1 : 0)` instead;
3. `-y` (the field's subtraction from zero) into `neg`, and `y = -y` if the
   digit is negative (the window's top bit is clear; always for a short last
   window);
4. `R = R + Q` by a call of the complete addition, `vg_<curve>_point_add`.

The only branches are on counters, and every address is `r3` plus a constant
and a public counter, or the table's address plus one: only the pointers may
affect timing. The registers written are `r4`–`r12` and `r31`, and those
the calls write.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

open VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Mont.PPC64LE
open Point

/-- A comb: the ladder's layout `L` (its `R`, `a`, `3b` and table of bits),
the field's functions `F`, windows of `w` bits, `J` of them, the table's
symbol, the start `S` (affine, in Montgomery's form), Montgomery's one, and
the slots of zero and of `-y`. -/
structure TCombCfg where
  L : LadderCfg
  F : Impl.Weierstrass.Mont.Modulus
  w : Nat
  J : Nat
  tsym : String
  start : Nat × Nat
  one : Nat
  zero : Nat
  neg : Nat
  /-- Where the entry is selected to: the point functions' `Q`, for curves
  whose coordinates fit them, else three slots of the inlined addition. -/
  qBase : Nat := Impl.Weierstrass.Point.qAt L.M.n

namespace TCombCfg

variable (K : TCombCfg)

/-- The digits' greatest magnitude, `2^(w-1)`. -/
def H : Nat := 2 ^ (K.w - 1)

/-- The point functions' points. -/
def P : Pt := ptAt K.L.M.n (Impl.Weierstrass.Point.pAt K.L.M.n)
def Q : Pt := ptAt K.L.M.n K.qBase
def O : Pt := ptAt K.L.M.n (Impl.Weierstrass.Point.oAt K.L.M.n)

/-- `r9 = Σ_{i<k} 2^i [r4 + bits + d + i]`, through `r5`. -/
def hornerAt : Nat → Nat → List Instr
  | _, 0 => [.li .r9 0]
  | d, k + 1 => hornerAt (d + 1) k ++ [.add .r9 .r9 .r9, .lbz .r5 .r4 (K.L.bits + d), .add .r9 .r9 .r5]

def horner (k : Nat) : List Instr := K.hornerAt 0 k

/-- The last window's bits. -/
def topBits : Nat := K.L.nbits - K.w * (K.J - 1)

/-- `r6 = r31 - (J - 1)`: zero for the last window. -/
def lastTest : List Instr := [.subi .r6 .r31 (K.J - 1)]

/-- The condition of the last window. -/
abbrev isLast : Cond := .zero .d .r6

/-- `r9 = |r9 - H|`, through `r4` and `r5`. -/
def magnitude : List Instr :=
  [.subi .r9 .r9 K.H, .lsr .d .r4 .r9 63, .li .r5 0, .sub .r4 .r5 .r4,
    .logic .xor .r9 .r9 .r4, .sub .r9 .r9 .r4]

/-- `r4 = r3 + w r31`: the window's bits, at `bits` from it. -/
def windowIndex : List Instr := [.li .r4 K.w, .mul .r4 .r4 .r31, .add .r4 wb .r4]

/-- The digit's magnitude `|k_j - H|` in `r9`. -/
def digit : Prog isa :=
  .seq (.block K.windowIndex) <|
  .seq (.block K.lastTest) <|
  .seq (.ite isLast (.block (K.horner K.topBits)) (.block (K.horner K.w))) (.block K.magnitude)

/-- The mask `r10` of `r9 = idx`, through `r5`. -/
def eqMask (idx : Reg) : List Instr :=
  [.logic .xor .r10 .r9 idx, .subi .r10 .r10 1, .lsr .d .r10 .r10 63, .li .r5 0, .sub .r10 .r5 .r10]

/-- Word `i` of `Q` or'ed with the table's at `r8` under the mask `r10`,
through `r4` and `r5`. -/
def selectWord (i : Nat) : List Instr :=
  [.load .d .r4 wb (K.Q.x + 8 * i), .load .d .r5 .r8 (8 * i),
    .logic .xor .r5 .r5 .r4, .logic .and .r5 .r5 .r10,
    .logic .xor .r4 .r4 .r5, .store .d .r4 wb (K.Q.x + 8 * i)]

/-- Entry `r7` of the row: its `2 n` words selected under the mask of
`r9 = r7`, then `r8` to the next entry, `r7 += 1` and `r6 = r7 - (H + 1)`. -/
def selectBody : List Instr :=
  eqMask .r7 ++ (List.range (2 * K.L.M.n)).flatMap K.selectWord ++
    [.addi .r8 .r8 (16 * K.L.M.n), .addi .r7 .r7 1, .subi .r6 .r7 (K.H + 1)]

/-- The row's address in `r8` (row `r31`), `Q`'s `x` and `y` zero, and
`r7 = 1`. -/
def selectSetup : List Instr :=
  [.adrSym .r8 K.tsym, .li .r4 (16 * K.L.M.n * K.H), .mul .r4 .r4 .r31, .add .r8 .r8 .r4] ++
    setConst K.L.M.n K.Q.x 0 ++ setConst K.L.M.n K.Q.y 0 ++ [.li .r7 1]

/-- `Z = 1`, and `Q = (0 : 1 : 0)` if the magnitude is zero. -/
def selectTail : List Instr :=
  setConst K.L.M.n K.Q.z K.one ++ [.li .r7 0] ++ eqMask .r7 ++
    sel K.L.M.n K.Q.y K.Q.y K.Q.z ++ sel K.L.M.n K.Q.z K.Q.z K.zero

/-- The entry of magnitude `r9` of row `r31` into `Q`. -/
def select : Prog isa :=
  .seq (.block K.selectSetup) (.seq (.loop (.block K.selectBody) (.nonzero .d .r6)) (.block K.selectTail))

/-- The mask `r10` of the window's top bit being clear (the digit is
negative), through `r4`. -/
def signRead : List Instr := K.windowIndex ++ [.lbz .r4 .r4 (K.L.bits + K.w - 1), .subi .r10 .r4 1]

/-- The digit's sign's mask: for a short last window, all ones. -/
def signMask : Prog isa :=
  if K.topBits < K.w then
    .seq (.block K.lastTest) (.ite isLast (.block [.li .r10 0, .subi .r10 .r10 1]) (.block K.signRead))
  else .block K.signRead

/-- The signed entry into `Q`. -/
def entry : Prog isa :=
  .seq K.digit <| .seq K.select <|
  .seq (subCall K.F K.neg K.zero K.Q.y) <|
  .seq K.signMask (.block (sel K.L.M.n K.Q.y K.Q.y K.neg))

/-- `R = R + Q` by a call of the complete addition. -/
def add : Prog isa :=
  .seq (.block (copyPt K.L.M.n K.P K.L.R)) <|
  .seq (ptCall K.F false) (.block (copyPt K.L.M.n K.L.R K.O))

/-- An iteration: `r31 -= 1`, the entry, the addition. -/
def step : Prog isa := .seq (.block [decCounter]) (.seq K.entry K.add)

/-- The comb: `a` and `3b` to the point functions' slots, `R = S`, then
the `J` iterations. -/
def comb : Prog isa :=
  .seq (.block (ladderSetup K.L ++ setConst K.L.M.n K.L.R.x K.start.1 ++ setConst K.L.M.n K.L.R.y K.start.2 ++
    setConst K.L.M.n K.L.R.z K.one ++ [.li .r31 K.J]))
    (.loop K.step more)

end TCombCfg

end VG.Impl.Weierstrass.PPC64LE
