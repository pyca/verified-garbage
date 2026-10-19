module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# Sums of polynomials stored with 16 bits, on AArch64

`accW op(f = x0, g = x1)`: `f[i] ← op(f[i], g[i])`, eight coefficients at a
time, with `q` in the halfwords of `v16`. In halfwords there is no UMIN, so
`x mod q` of an `x < 2q` is `x - (x ≥ q ? q : 0)`: CMHS against `q`, AND
with `q`, SUB (`hcsub`).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.AddSubW
open VG VG.AArch64

/-- `v2 ← v2 mod q`, for halfwords less than `2q`, through `v3`. -/
def hcsub : List Instr :=
  [.vop (.cmp .hs .h8 .v3 .v2 .v16), .vop (.logic .and .v3 .v3 .v16), .vop (.sub .h8 .v2 .v2 .v3)]

/-- `v2 ← (v0 + v1) mod q`. -/
def haddOp : List Instr := .vop (.add .h8 .v2 .v0 .v1) :: hcsub

def accBodyW (op : List Instr) : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x1 0] ++ op ++
    [.strq .v2 .x0 0, .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 16, .subImm .x .x11 .x11 1]

def accW (op : List Instr) : Prog isa :=
  .seq (.block [.movz .x .x9 3329 0, .vop (.dup .h8 .v16 .x9), .movz .x .x11 32 0])
    (.loop (.block (accBodyW op)) (.nonzero .x .x11))

def addW : Prog isa := accW haddOp

end VG.Impl.MlKem.AArch64.AddSubW
