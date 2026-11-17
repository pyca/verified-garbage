module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb

/-!
# `[k]G` by the comb, with the addition inlined, on 32-bit ARM

The comb of `Impl/Weierstrass/Arm/TComb.lean` for curves whose coordinates
do not fit the point functions' slots (more than 6 words), as the ladder
runs them (`ladder`, `Impl/Weierstrass/Arm.lean`): the same window, digit,
scan and sign, the entry selected to three of the ladder's slots (`qBase`),
and `R = R + Q` by the complete addition inlined (`rcb`, the field's calls)
into the ladder's `D`, then copied to `R`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Arm

open VG.Arm VG.Impl.Weierstrass VG.Impl.Mont.Arm
open Point

namespace TCombCfg

variable (K : TCombCfg)

/-- `R = R + Q` by the inlined complete addition, into `D`, then `R = D`. -/
def addI : Prog isa :=
  .seq (fprog K.F (rcb K.L.S K.L.R K.Q K.L.D) K.u) (.block (copyPt K.L.M.n K.L.R K.L.D))

/-- An iteration: `r11 -= 1`, the entry, the addition, and the counter's test. -/
def stepI : Prog isa :=
  .seq (.block [decCounter]) <| .seq K.entry <| .seq K.addI (.block [testCounter])

/-- The comb: `R = S`, then the `J` iterations (`a` and `3b` are the
ladder's, which the setup writes). -/
def combI : Prog isa :=
  .seq (.block (setConst K.L.M.n K.L.R.x K.start.1 ++ setConst K.L.M.n K.L.R.y K.start.2 ++
    setConst K.L.M.n K.L.R.z K.one ++ [.mov .r11 (.imm (BitVec.ofNat 32 K.J))]))
    (.loop K.stepI .ne)

end TCombCfg

end VG.Impl.Weierstrass.Arm
