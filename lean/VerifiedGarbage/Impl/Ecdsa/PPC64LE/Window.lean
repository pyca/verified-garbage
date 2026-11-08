module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-!
# `[k]P` by four-bit windows, on PPC64LE

`R = [k]P` for a curve with `a = -3`, on the signature's layout of the
working space (`Impl/Ecdsa/PPC64LE.lean`), in place of the ladder over every
bit, as on RISC-V (`Impl/Ecdsa/RISCV64/Window.lean`): `P` affine at the slots
`gx`, `gy` (and `ONEP` for `Z = 1`), `b` in Montgomery's form at the slot
`bp`, `k`'s bits in the table of bits at `bitsAt n 0` (one byte each), and the
result in `R`.

1. The table of `[e]P` for `e < 16`, past the tables of bits (`entry e`,
   `24 n` bytes each, from `bitsAt n 3`): `O = (0 : 1 : 0)` and
   `P = (x : y : 1)` copied in, then `D = P` and, for `e` from 2 to 15,
   `T = D + P` by the complete addition for `a = -3` (`rcb3`), copied to
   entry `e` and to `D`.
2. From `R = O`, for the windows `j` from `16 n - 1` down to 0 (the counter
   `r31 = j + 1`, then `j`), `R = 16 R + [k_j]P` for the nibble `k_j` of `k`:
   * `R = 16 R` (`quad`): `R` in Jacobian coordinates in `D` (`toJ`), four
     doublings between `D` and `T` (`dblJ`, dbl-2001-b), back in projective
     coordinates in `R` (`fromJ`), and `Y = 1` where `Z = 0` (the double of
     `O`);
   * the nibble into `r9` (`nibble`: its four bits from the table of bits,
     at `4 j` from it, by Horner's rule), and every entry `e` scanned
     (`scan`): `D = entry e` under the mask of `k_j = e` (`eqMask`), so that
     `D` holds entry `k_j`;
   * `T = R + D` by the complete addition, copied to `R`.

The field operations are calls of the functions of `p`
(`Impl/Weierstrass/PPC64LE/Call.lean`). The only branch is on the counter,
and every address is `r3` plus a constant, plus `4 j` for the nibble's bits:
only the pointer may affect timing. The registers written are `r31` and those
the calls write (`r0`, `r4`–`r12`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE.Window

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- The table's start: past the three tables of bits. -/
def tblAt : Nat := bitsAt c.n 3

/-- The bytes of an entry. -/
def eb : Nat := 24 * c.n

/-- Entry `e` of the table. -/
def entry (e : Nat) : Pt := ⟨tblAt c + eb c * e, tblAt c + eb c * e + 8 * c.n, tblAt c + eb c * e + 16 * c.n⟩

/-- The complete addition's slots, with `b R mod p` at the slot `bp` (`rcb3`
reads it as `S.b3`). -/
def slots (bp : Nat) : RcbSlots :=
  ⟨c.sl AP, c.sl bp, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5⟩

/-- Zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := c.pt ZERO ZERO ZERO

/-- `R`, `D` and `T`. -/
def rPt : Pt := c.pt RX RY RZ
def dPt : Pt := c.pt DX DY DZ
def tPt : Pt := c.pt TX TY TZ

/-- `o = p`. -/
def copyPt (o p : Pt) : List Instr := Point.copyPt c.n o p

/-- `T = D + G`, copied to entry `e + 2` and to `D`, for `e` from 0 up to
`e`. -/
def adds (gx gy bp : Nat) : Nat → Prog isa
  | 0 => .block []
  | e + 1 => .seq (adds gx gy bp e) <|
      .seq (fprog c.SP (rcb3 (slots c bp) (dPt c) (c.pt gx gy ONEP) (tPt c)))
        (.block (copyPt c (entry c (e + 2)) (tPt c) ++ copyPt c (dPt c) (tPt c)))

/-- The table: `O`, `P`, and `[e]P` for `e = 2 … 15`. -/
def build (gx gy bp : Nat) : Prog isa :=
  .seq (.block (copyPt c (entry c 0) (c.pt ZERO ONEP ZERO) ++ copyPt c (entry c 1) (c.pt gx gy ONEP) ++
    copyPt c (dPt c) (c.pt gx gy ONEP)))
    (adds c gx gy bp 14)

/-- `R = 16 R`: to Jacobian coordinates in `D`, four doublings between `D`
and `T`, back to `R`, then `Y = 1` where `Z` is zero (the mask of `Z ≠ 0`
in `r10`). -/
def quad (bp : Nat) : Prog isa :=
  let S := slots c bp
  progs [fprog c.SP (toJ S (rPt c) (zeroPt c) (dPt c)), fprog c.SP (dblJ S (dPt c) (tPt c)),
    fprog c.SP (dblJ S (tPt c) (dPt c)), fprog c.SP (dblJ S (dPt c) (tPt c)),
    fprog c.SP (dblJ S (tPt c) (dPt c)), fprog c.SP (fromJ S (dPt c) (zeroPt c) (rPt c)),
    .block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY))]

/-- The nibble `k_j` into `r9`, for `j` in `r31`: its bits, bytes `4 j + i`
of the table of bits (through `r4 = r3 + 4 j` and `r5`), by Horner's rule. -/
def nibble : List Instr :=
  [.lsl .r4 .r31 2, .add .r4 wb .r4, .lbz .r9 .r4 (bitsAt c.n 0 + 3),
    .add .r9 .r9 .r9, .lbz .r5 .r4 (bitsAt c.n 0 + 2), .add .r9 .r9 .r5,
    .add .r9 .r9 .r9, .lbz .r5 .r4 (bitsAt c.n 0 + 1), .add .r9 .r9 .r5,
    .add .r9 .r9 .r9, .lbz .r5 .r4 (bitsAt c.n 0), .add .r9 .r9 .r5]

/-- The mask `r10` of `r9 = e`, through `r5`. -/
def eqMask (e : Nat) : List Instr :=
  [.li .r5 e, .logic .xor .r10 .r9 .r5, .subi .r10 .r10 1, .lsr .d .r10 .r10 63, .li .r5 0,
    .sub .r10 .r5 .r10]

/-- Entry `e` to `D` under the mask of `r9 = e`. -/
def scanEntry (e : Nat) : List Instr := eqMask e ++ selPt c.n (dPt c) (dPt c) (entry c e)

/-- Entry `k_j` to `D`: the nibble, then the sixteen entries scanned. -/
def select : List Instr := nibble c ++ (List.range 16).flatMap (scanEntry c)

/-- One window: `r31 -= 1`, `R = 16 R`, the entry `D` of the nibble, and
`R = R + D` (through `T`). -/
def step (bp : Nat) : Prog isa :=
  .seq (.block [decCounter]) <|
  .seq (quad c bp) <|
  .seq (.block (select c)) <|
  .seq (fprog c.SP (rcb3 (slots c bp) (rPt c) (dPt c) (tPt c))) (.block (copyPt c (rPt c) (tPt c)))

/-- The number of windows of `k`. -/
def windows : Nat := 16 * c.n

/-- `R = [k]P`: the table, `R = O`, then the windows. -/
def mul (gx gy bp : Nat) : Prog isa :=
  .seq (build c gx gy bp) <|
  .seq (.block (copyPt c (rPt c) (c.pt ZERO ONEP ZERO) ++ [.li .r31 (windows c)]))
    (.loop (step c bp) more)

end Cfg

end VG.Impl.Ecdsa.PPC64LE.Window
