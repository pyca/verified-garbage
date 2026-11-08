module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Mont.PPC64LE

/-!
# `[u]G + [v]Q` by one chain of doublings, on PPC64LE

Shamir's trick: from the top bit `t` down, `R = 2R + E` for the entry `E`
of the bit pair `(u_t, v_t)`: `O`, `G`, `Q` or `G + Q`, selected by masks.
The doubling and the addition are calls of the point functions (`ptCall`),
whose complete formulas need no case for `R = E` or for the point at
infinity, so for curves whose coordinates fit their slots (at most 6 words,
as `ladderP`). Two complete additions a bit, where two ladders take four,
and constant time: every address is `r3` plus a constant or the counter.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE.Point

open VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open Impl.Weierstrass.Point (aAt b3At oAt pAt qAt)

/-- The joint multiplication's slots: the ladder's (`G`, affine, the
accumulator `R`, the temporaries `D` and `T`, `a`, `3b`, and the table of `u`'s bits),
`Q` (affine), `G + Q`, the point at infinity `O = (0 : 1 : 0)`, the table of
`v`'s bits, and `R mod p`, Montgomery's one. -/
structure JointCfg where
  L : LadderCfg
  Q : Pt
  GQ : Pt
  O : Pt
  bitsV : Nat
  one : Nat

namespace JointCfg

variable (J : JointCfg)

/-- The point functions' slots. -/
def fP : Pt := ptAt J.L.M.n (pAt J.L.M.n)
def fQ : Pt := ptAt J.L.M.n (qAt J.L.M.n)
def fO : Pt := ptAt J.L.M.n (oAt J.L.M.n)

/-- `a` and `3b` to the point functions' slots, `G` to `P` and `Q` to `Q`. -/
def setup : List Instr :=
  copy J.L.M.n (aAt J.L.M.n) J.L.S.a ++ copy J.L.M.n (b3At J.L.M.n) J.L.S.b3 ++
  copyPt J.L.M.n J.fP J.L.G ++ copyPt J.L.M.n J.fQ J.Q

/-- `G + Q` saved, `R = O = (0 : 1 : 0)`, and the counter. -/
def start : List Instr :=
  copyPt J.L.M.n J.GQ J.fO ++
  VG.Impl.Mont.PPC64LE.setConst J.L.M.n J.L.R.x 0 ++ VG.Impl.Mont.PPC64LE.setConst J.L.M.n J.L.R.y J.one ++
  VG.Impl.Mont.PPC64LE.setConst J.L.M.n J.L.R.z 0 ++ [.li .r31 J.L.nbits]

/-- `Q = ` the entry of the bits `(u_t, v_t)` of `t = r31`, by masks:
`T = u_t ? G : O` and `D = u_t ? G + Q : Q`, then `Q = v_t ? D : T`. -/
def select : List Instr :=
  bitMask J.L.bits ++ selPt J.L.M.n J.L.T J.O J.L.G ++ selPt J.L.M.n J.L.D J.Q J.GQ ++
  bitMask J.bitsV ++ selPt J.L.M.n J.fQ J.L.T J.L.D

/-- One position `t = r31 - 1`: `P = R`, `O = P + P`, `P = O`, the entry to
`Q`, `O = P + Q`, `R = O`. -/
def body (S : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block (decCounter :: copyPt J.L.M.n J.fP J.L.R)) <|
  .seq (ptCall S true) <|
  .seq (.block (copyPt J.L.M.n J.fP J.fO ++ J.select)) <|
  .seq (ptCall S false) (.block (copyPt J.L.M.n J.L.R J.fO))

/-- `[u]G + [v]Q` into `R`, from the tables of the bits of `u` and `v`. -/
def joint (S : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block J.setup) <| .seq (ptCall S false) <| .seq (.block J.start) (.loop (J.body S) more)

end JointCfg

end VG.Impl.Weierstrass.PPC64LE.Point
