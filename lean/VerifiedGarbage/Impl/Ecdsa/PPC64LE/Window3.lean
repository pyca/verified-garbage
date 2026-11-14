module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window

/-!
# `[k]P` by three-bit windows, on PPC64LE

The windows of `Impl/Ecdsa/PPC64LE/Window.lean` three bits at a time, for a
curve whose sixteen entries of four-bit windows do not fit the working space
past the tables of bits (P-521's: coordinates of nine words, entries of
`24 n = 216` bytes): the table of `[e]P` for `e < 8` (`build3`: `O`, `P`
and six complete additions), and for the windows `j` from `windows3` down to
0, `R = 8 R` (`trip`: `toJ`, three doublings, `fromJ`, `Y = 1` where
`Z = 0`), the entry of the three bits `k_j` (`select3`: bits `3 j` to
`3 j + 2` of the table of bits, the eight entries scanned under masks), and
`R = R + D` by the complete addition. As for the four-bit windows, the only
branch is on the counter and every address is `r3` plus a constant, plus
`3 j` for the window's bits.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE.Window

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- The table: `O`, `P`, and `[e]P` for `e = 2 … 7`. -/
def build3 (gx gy bp : Nat) : Prog isa :=
  .seq (.block (copyPt c (entry c 0) (c.pt ZERO ONEP ZERO) ++ copyPt c (entry c 1) (c.pt gx gy ONEP) ++
    copyPt c (dPt c) (c.pt gx gy ONEP)))
    (adds c gx gy bp 6)

/-- `R = 8 R`: to Jacobian coordinates in `D`, three doublings (`D` to `T`,
back, and to `T` again), back to `R` from `T`, then `Y = 1` where `Z` is
zero. -/
def trip (bp : Nat) : Prog isa :=
  let S := slots c bp
  progs [fprog c.SP (toJ S (rPt c) (zeroPt c) (dPt c)), fprog c.SP (dblJ S (dPt c) (tPt c)),
    fprog c.SP (dblJ S (tPt c) (dPt c)), fprog c.SP (dblJ S (dPt c) (tPt c)),
    fprog c.SP (fromJ S (tPt c) (zeroPt c) (rPt c)),
    .block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY))]

/-- The window `k_j` into `r9`, for `j` in `r31`: bits `3 j + i` of the
table of bits (through `r4 = r3 + 3 j` and `r5`), by Horner's rule. -/
def nibble3 : List Instr :=
  [.lsl .r4 .r31 1, .add .r4 .r4 .r31, .add .r4 wb .r4, .lbz .r9 .r4 (bitsAt c.n 0 + 2),
    .add .r9 .r9 .r9, .lbz .r5 .r4 (bitsAt c.n 0 + 1), .add .r9 .r9 .r5,
    .add .r9 .r9 .r9, .lbz .r5 .r4 (bitsAt c.n 0), .add .r9 .r9 .r5]

/-- Entry `k_j` to `D`: the window, then the eight entries scanned. -/
def select3 : List Instr := nibble3 c ++ (List.range 8).flatMap (scanEntry c)

/-- One window: `r31 -= 1`, `R = 8 R`, the entry `D`, and `R = R + D`
(through `T`). -/
def step3 (bp : Nat) : Prog isa :=
  .seq (.block [decCounter]) <|
  .seq (trip c bp) <|
  .seq (.block (select3 c)) <|
  .seq (fprog c.SP (rcb3 (slots c bp) (rPt c) (dPt c) (tPt c))) (.block (copyPt c (rPt c) (tPt c)))

/-- The number of three-bit windows of the bytes of a scalar: `8 len / 3`
(rounded up). -/
def windows3 : Nat := (8 * c.C.len + 2) / 3

/-- `R = [k]P` by three-bit windows: the table, `R = O`, then the windows. -/
def mul3 (gx gy bp : Nat) : Prog isa :=
  .seq (build3 c gx gy bp) <|
  .seq (.block (copyPt c (rPt c) (c.pt ZERO ONEP ZERO) ++ [.li .r31 (windows3 c)]))
    (.loop (step3 c bp) more)

end Cfg

end VG.Impl.Ecdsa.PPC64LE.Window
