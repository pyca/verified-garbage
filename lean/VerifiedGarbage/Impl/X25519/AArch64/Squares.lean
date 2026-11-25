module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Two squares modulo 2²⁵⁵ - 19 in AdvSIMD

`squares a b` squares the elements of four 64-bit words at offsets `a` and `b`
of the working space (`x0`), into five limbs of 51 bits each at `OUT` and
`OUT + 48` (the last of the six words there is padding); lane `e` of each
vector belongs to element `e`.

Each element is split into ten limbs of 26 and 25 bits by turns, at bits
`51 k` and `51 k + 26`: vector `av k` holds the low limbs of both elements in
its low words and the high ones in its high words, so that `umull` multiplies
low limbs, `umull2` high limbs, and, with the halves of one operand exchanged,
the two products of a low and a high limb. Column `ev m` collects what stands
at bit `51 m` (low by low, and twice high by high, one limb up), `cv m` what
stands at bit `51 m + 26`; what is past bit 255 is taken with 19 times a limb.
One round of carries by 26 and 25 bits, all columns at once, and one by 51
bits leave the limbs just above 51 bits.

The masks and 19 are in the working space (`constants`). The code uses every
vector register and no general-purpose one but `x0`.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Squares

open VG.AArch64

/-- The results: five limbs of each element, 48 bytes apart. -/
def OUT : Nat := 1024
/-- `2⁵¹ - 1`, `2²⁶ - 1`, `2²⁵ - 1`, in both lanes of a vector, and 19 in each of its four words. -/
def K51 : Nat := 1120
def K26 : Nat := 1136
def K25 : Nat := 1152
def K19 : Nat := 1168

def vo (op : VOp) : Instr := .vop op
def ldq (t : VReg) (off : Nat) : Instr := .ldrq t .x0 off
def stq (t : VReg) (off : Nat) : Instr := .strq t .x0 off
def band (d n m : VReg) : Instr := vo (.logic .and d n m)
def ushr (d n : VReg) (k : Nat) : Instr := vo (.shift .ushr .d2 d n k)
def shl (d n : VReg) (k : Nat) : Instr := vo (.shift .shl .d2 d n k)
def sri (d n : VReg) (k : Nat) : Instr := vo (.shift .sri .d2 d n k)
def add2 (d n m : VReg) : Instr := vo (.add .d2 d n m)
def trn1 (d n m : VReg) : Instr := vo (.perm .trn1 .d2 d n m)
def trn2 (d n m : VReg) : Instr := vo (.perm .trn2 .d2 d n m)
def uzp (d n m : VReg) : Instr := vo (.perm .uzp1 .s4 d n m)

/-- The limbs, `2` times them with the halves exchanged, `2` times and `19` times them. -/
def av : Nat → VReg | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | _ => .v4
def xv : Nat → VReg | 0 => .v5 | 1 => .v6 | 2 => .v7 | 3 => .v8 | _ => .v9
def dv : Nat → VReg | 0 => .v10 | 1 => .v11 | 2 => .v12 | 3 => .v13 | _ => .v14
def nv : Nat → VReg | 0 => .v15 | 1 => .v16 | 2 => .v17 | 3 => .v18 | _ => .v19
/-- The columns at bits `51 m` and `51 m + 26`. -/
def ev : Nat → VReg | 0 => .v20 | 1 => .v21 | 2 => .v22 | 3 => .v23 | _ => .v24
def cv : Nat → VReg | 0 => .v25 | 1 => .v26 | 2 => .v27 | 3 => .v28 | _ => .v29

/-- The words of both elements, word `i` in `v(24 + i)`. -/
def words (a b : Nat) : List Instr :=
  [ldq .v31 K26, ldq .v30 K25, ldq .v20 a, ldq .v21 b, ldq .v22 (a + 16), ldq .v23 (b + 16),
    trn1 .v24 .v20 .v21, trn2 .v25 .v20 .v21, trn1 .v26 .v22 .v23, trn2 .v27 .v22 .v23]

/-- The limbs. -/
def split : List Instr :=
  [band .v20 .v24 .v31, ushr .v21 .v24 26, band .v21 .v21 .v30, uzp .v0 .v20 .v21,
    shl .v20 .v25 13, sri .v20 .v24 51, band .v20 .v20 .v31, ushr .v21 .v25 13, band .v21 .v21 .v30, uzp .v1 .v20 .v21,
    ushr .v20 .v25 38, band .v21 .v26 .v30, uzp .v2 .v20 .v21,
    ushr .v20 .v26 25, band .v20 .v20 .v31, shl .v21 .v27 13, sri .v21 .v26 51, band .v21 .v21 .v30, uzp .v3 .v20 .v21,
    ushr .v20 .v27 12, band .v20 .v20 .v31, ushr .v21 .v27 38, uzp .v4 .v20 .v21]

/-- Twice the limbs, those exchanged, and 19 times the limbs. -/
def multiples : List Instr :=
  ((List.range 5).map fun k => vo (.add .s4 (dv k) (av k) (av k))) ++
    (((List.range 5).map fun k => vo (.ext (xv k) (dv k) (dv k) 8)) ++
      ldq .v31 K19 :: (List.range 5).map fun k => vo (.mul (nv k) (av k) .v31))

/-- A product: of the high words (`hi`) or the low ones of two registers. -/
abbrev Term := Bool × VReg × VReg

/-- The pairs `i ≤ j` of limbs with `i + j` equal to `m` modulo 5. -/
def pairs (m : Nat) : List (Nat × Nat) :=
  (List.range 5).filterMap fun i => let j := (m + 5 - i) % 5; if i ≤ j then some (i, j) else none

/-- The second factor of limbs `i` and `j`, with 19 if the product is past limb 4. -/
def second (j s : Nat) : VReg := if 5 ≤ s then nv j else av j

/-- The products of high limbs one column up, not doubled; of low limbs; of a low and a high one. -/
def highs (m : Nat) : List Term :=
  (pairs (m + 4)).map fun (i, j) => (true, if i = j then av i else dv i, second j (i + j + 1))
def lows (m : Nat) : List Term :=
  (pairs m).map fun (i, j) => (false, if i = j then av i else dv i, second j (i + j))
def crosses (m : Nat) : List Term :=
  (pairs m).flatMap fun (i, j) =>
    if i = j then [(false, xv i, second j (i + j))]
    else [(false, xv i, second j (i + j)), (true, xv i, second j (i + j))]

def mla (d : VReg) (p : Term) : Instr := vo (.umlal p.1 d p.2.1 p.2.2)
/-- The sum of the products in `d`. -/
def msum (d : VReg) : List Term → List Instr
  | [] => []
  | p :: ps => vo (.umull p.1 d p.2.1 p.2.2) :: ps.map (mla d)

def column (m : Nat) : List Instr :=
  msum (ev m) (highs m) ++ add2 (ev m) (ev m) (ev m) :: ((lows m).map (mla (ev m)) ++ msum (cv m) (crosses m))

def columns : List Instr := (List.range 5).flatMap column

/-- The round of carries by 26 and 25 bits; what leaves the last column, times 19, into the first. -/
def carry1 : List Instr :=
  [ldq .v3 K26, ldq .v4 K25, ushr .v2 .v29 25, band .v29 .v29 .v4,
    ushr .v0 .v24 26, band .v24 .v24 .v3, add2 .v29 .v29 .v0,
    ushr .v1 .v28 25, band .v28 .v28 .v4, add2 .v24 .v24 .v1, ushr .v0 .v23 26, band .v23 .v23 .v3, add2 .v28 .v28 .v0,
    ushr .v1 .v27 25, band .v27 .v27 .v4, add2 .v23 .v23 .v1, ushr .v0 .v22 26, band .v22 .v22 .v3, add2 .v27 .v27 .v0,
    ushr .v1 .v26 25, band .v26 .v26 .v4, add2 .v22 .v22 .v1, ushr .v0 .v21 26, band .v21 .v21 .v3, add2 .v26 .v26 .v0,
    ushr .v1 .v25 25, band .v25 .v25 .v4, add2 .v21 .v21 .v1, ushr .v0 .v20 26, band .v20 .v20 .v3, add2 .v25 .v25 .v0,
    add2 .v20 .v20 .v2, shl .v0 .v2 1, shl .v2 .v2 4, add2 .v20 .v20 .v0, add2 .v20 .v20 .v2]

/-- The limbs of 51 bits. -/
def join : List Instr :=
  (List.range 5).flatMap fun m => [shl (cv m) (cv m) 26, add2 (ev m) (ev m) (cv m)]

/-- The round of carries by 51 bits. -/
def carry2 : List Instr :=
  ldq .v5 K51 :: ((List.range 5).flatMap fun m => [ushr (cv m) (ev m) 51, band (ev m) (ev m) .v5]) ++
    [add2 .v21 .v21 .v25, add2 .v22 .v22 .v26, add2 .v23 .v23 .v27, add2 .v24 .v24 .v28,
      add2 .v20 .v20 .v29, shl .v0 .v29 1, shl .v2 .v29 4, add2 .v20 .v20 .v0, add2 .v20 .v20 .v2]

/-- The limbs of element `e` at `OUT + 48 e`. -/
def stores : List Instr :=
  [trn1 .v0 .v20 .v21, trn2 .v1 .v20 .v21, stq .v0 OUT, stq .v1 (OUT + 48),
    trn1 .v0 .v22 .v23, trn2 .v1 .v22 .v23, stq .v0 (OUT + 16), stq .v1 (OUT + 64),
    trn1 .v0 .v24 .v24, trn2 .v1 .v24 .v24, stq .v0 (OUT + 32), stq .v1 (OUT + 80)]

def squares (a b : Nat) : List Instr :=
  words a b ++ (split ++ (multiples ++ (columns ++ (carry1 ++ (join ++ (carry2 ++ stores))))))

/-! ## Around them -/

/-- The five limbs at `o` into `x2, x3, x8, x9, x16`. -/
def packLoad (o : Nat) : List Instr :=
  [.ldr .x .x2 .x0 o, .ldr .x .x3 .x0 (o + 8), .ldr .x .x8 .x0 (o + 16), .ldr .x .x9 .x0 (o + 24),
    .ldr .x .x16 .x0 (o + 32)]

/-- Those as four words in `d0`–`d3`; `x2, x3, x8, x9, x16, x17` are clobbered. -/
def packSum (d0 d1 d2 d3 : Reg) : List Instr :=
  [.lsl .x .x17 .x3 51, .adds .x d0 .x2 .x17, .lsr .x .x3 .x3 13, .lsl .x .x17 .x8 38, .adcs .x d1 .x3 .x17,
    .lsr .x .x8 .x8 26, .lsl .x .x17 .x9 25, .adcs .x d2 .x8 .x17, .lsr .x .x9 .x9 39, .lsl .x .x17 .x16 12,
    .adc .x d3 .x9 .x17]

/-- The word `x` in both lanes of the vector at `o`. -/
def constant (o : Nat) (x : BitVec 64) : List Instr :=
  [.movz .x .x4 (x.extractLsb' 0 16) 0, .movk .x .x4 (x.extractLsb' 16 16) 1, .movk .x .x4 (x.extractLsb' 32 16) 2,
    .movk .x .x4 (x.extractLsb' 48 16) 3, vo (.dup .d2 .v0 .x4), stq .v0 o]

def constants : List Instr :=
  constant K51 0x7ffffffffffff ++ (constant K26 0x3ffffff ++ (constant K25 0x1ffffff ++ constant K19 0x1300000013))

/-- Where `v8`–`v15` are saved. -/
def VSAVE : Nat := 1184
def vsaved : Nat → VReg
  | 0 => .v8 | 1 => .v9 | 2 => .v10 | 3 => .v11 | 4 => .v12 | 5 => .v13 | 6 => .v14 | _ => .v15
def vsave : List Instr := (List.range 8).flatMap fun k => [stq (vsaved k) (VSAVE + 16 * k)]
def vrestore : List Instr := (List.range 8).flatMap fun k => [ldq (vsaved k) (VSAVE + 16 * k)]

end VG.Impl.X25519.AArch64.Squares
