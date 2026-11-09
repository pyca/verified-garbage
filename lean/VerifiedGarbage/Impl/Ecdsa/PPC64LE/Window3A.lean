module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA

/-!
# `[k]P` by three-bit windows on PPC64LE, for any `a`

`Window3.lean`'s three-bit windows for a curve with any `a` whose sixteen
entries of four-bit windows do not fit the working space past the tables of
bits (brainpoolP512r1's: coordinates of eight words, entries of `24 n = 192`
bytes, sixteen of which would end past 8192): the same table of eight
entries, windows and scan (`Window.Cfg.entry`, `select3`, `scanEntry`), with
`WindowA.lean`'s complete addition for any `a` (`rcb`, `a` at `AP` and `3 b`
at the slot `b3`, `B3P` in the signature's layout) and Jacobian doubling for
any `a` (`dblJa`) in place of `rcb3` and `dblJ`.

`mul3top`, for a scalar of `3 w + 2` bits (brainpoolP512r1's 512): `w`
windows from `R = O`, as `Window3.lean`'s `mul3`, would read a 513th bit,
past the table of bits, in the top window. So `R` starts at the entry of the
top two bits (`top2`, then the scan), and the `w` windows below them follow.
As for `Window3.lean`, the only branch is on the counter, and every address
is `r3` plus a constant, plus `3 j` for the window's bits.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE.WindowA

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE
open VG.Impl.Ecdsa.PPC64LE.Window.Cfg (slots entry zeroPt rPt dPt tPt copyPt select3 scanEntry)

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- The table: `O`, `P`, and `[e]P` for `e = 2 … 7`. -/
def build3 (gx gy b3 : Nat) : Prog isa :=
  .seq (.block (copyPt c (entry c 0) (c.pt ZERO ONEP ZERO) ++ copyPt c (entry c 1) (c.pt gx gy ONEP) ++
    copyPt c (dPt c) (c.pt gx gy ONEP)))
    (adds c gx gy b3 6)

/-- `R = 8 R`, by three doublings for any `a` (`D` to `T`, back, and to `T`
again), back to `R` from `T`, then `Y = 1` where `Z` is zero. -/
def trip (b3 : Nat) : Prog isa :=
  let S := slots c b3
  progs [fprog c.SP (toJ S (rPt c) (zeroPt c) (dPt c)), fprog c.SP (dblJa S (dPt c) (tPt c)),
    fprog c.SP (dblJa S (tPt c) (dPt c)), fprog c.SP (dblJa S (dPt c) (tPt c)),
    fprog c.SP (fromJ S (tPt c) (zeroPt c) (rPt c)),
    .block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY))]

/-- One window: `r31 -= 1`, `R = 8 R`, the entry `D` of the three bits, and
`R = R + D` (through `T`). -/
def step3 (b3 : Nat) : Prog isa :=
  .seq (.block [decCounter]) <|
  .seq (trip c b3) <|
  .seq (.block (select3 c)) <|
  .seq (fprog c.SP (rcb (slots c b3) (rPt c) (dPt c) (tPt c))) (.block (copyPt c (rPt c) (tPt c)))

/-- The three-bit windows below a scalar's top two bits, for scalars of
`3 w + 2` bits (brainpoolP512r1's 512): `8 len / 3`. -/
def windows3t : Nat := 8 * c.C.len / 3

/-- The scalar's top two bits, `k >>> 3 w` for `w = windows3t`, into `r9`:
bits `3 w + 1` and `3 w` of the table of bits, by Horner's rule. -/
def top2 : List Instr :=
  [.lbz .r9 wb (bitsAt c.n 0 + 3 * windows3t c + 1), .add .r9 .r9 .r9,
    .lbz .r5 wb (bitsAt c.n 0 + 3 * windows3t c), .add .r9 .r9 .r5]

/-- `R = [k]P` by three-bit windows, for a scalar of `3 w + 2` bits: the
table, `R` the entry of the top two bits (scanned as a window's), then the
`w` windows below them. Every window's bits are in the table of bits: `w`
windows from `R = O` would end with one bit past it. -/
def mul3top (gx gy b3 : Nat) : Prog isa :=
  .seq (build3 c gx gy b3) <|
  .seq (.block (top2 c ++ (List.range 8).flatMap (scanEntry c) ++ copyPt c (rPt c) (dPt c) ++
    [.li .r31 (windows3t c)]))
    (.loop (step3 c b3) more)

end Cfg

end VG.Impl.Ecdsa.PPC64LE.WindowA
