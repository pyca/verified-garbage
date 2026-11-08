module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window
public import VerifiedGarbage.Impl.Weierstrass.JacDblA

/-!
# `[k]P` by four-bit windows on PPC64LE, for any `a`

`Window.lean`'s windows for a curve with any `a` (the brainpool curves), as
RISC-V's `Impl/Ecdsa/RISCV64/WindowA.lean` is for RISC-V's: the same table,
nibbles, scan and loop (`Window.Cfg.entry`, `select`, `copyPt`), with the
complete addition for any `a` (`rcb`, which reads `a` at `AP` and `3 b` at
the slot `b3`, `B3P` in the signature's layout) in place of `rcb3`, and
the Jacobian doubling for any `a` (`dblJa`, dbl-2007-bl, `a` at `AP`) in
place of `dblJ`. As there, the only branch is on the counter, and every
address is `r3` plus a constant, plus `4 j` for the nibble's bits.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE.WindowA

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE
open VG.Impl.Ecdsa.PPC64LE.Window.Cfg (slots entry zeroPt rPt dPt tPt copyPt select windows)

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- `T = D + G`, copied to entry `e + 2` and to `D`, for `e` from 0 up to
`e`, by the complete addition for any `a`. -/
def adds (gx gy b3 : Nat) : Nat → Prog isa
  | 0 => .block []
  | e + 1 => .seq (adds gx gy b3 e) <|
      .seq (fprog c.SP (rcb (slots c b3) (dPt c) (c.pt gx gy ONEP) (tPt c)))
        (.block (copyPt c (entry c (e + 2)) (tPt c) ++ copyPt c (dPt c) (tPt c)))

/-- The table: `O`, `P`, and `[e]P` for `e = 2 … 15`. -/
def build (gx gy b3 : Nat) : Prog isa :=
  .seq (.block (copyPt c (entry c 0) (c.pt ZERO ONEP ZERO) ++ copyPt c (entry c 1) (c.pt gx gy ONEP) ++
    copyPt c (dPt c) (c.pt gx gy ONEP)))
    (adds c gx gy b3 14)

/-- `R = 16 R`, by four doublings for any `a`, then `Y = 1` where `Z` is zero. -/
def quad (b3 : Nat) : Prog isa :=
  let S := slots c b3
  progs [fprog c.SP (toJ S (rPt c) (zeroPt c) (dPt c)), fprog c.SP (dblJa S (dPt c) (tPt c)),
    fprog c.SP (dblJa S (tPt c) (dPt c)), fprog c.SP (dblJa S (dPt c) (tPt c)),
    fprog c.SP (dblJa S (tPt c) (dPt c)), fprog c.SP (fromJ S (dPt c) (zeroPt c) (rPt c)),
    .block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY))]

/-- One window: `r31 -= 1`, `R = 16 R`, the entry `D` of the nibble, and
`R = R + D` (through `T`). -/
def step (b3 : Nat) : Prog isa :=
  .seq (.block [decCounter]) <|
  .seq (quad c b3) <|
  .seq (.block (select c)) <|
  .seq (fprog c.SP (rcb (slots c b3) (rPt c) (dPt c) (tPt c))) (.block (copyPt c (rPt c) (tPt c)))

/-- `R = [k]P`: the table, `R = O`, then the windows. -/
def mul (gx gy b3 : Nat) : Prog isa :=
  .seq (build c gx gy b3) <|
  .seq (.block (copyPt c (rPt c) (c.pt ZERO ONEP ZERO) ++ [.li .r31 (windows c)]))
    (.loop (step c b3) more)

end Cfg

end VG.Impl.Ecdsa.PPC64LE.WindowA
