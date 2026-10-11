module

public import VerifiedGarbage.Impl.Weierstrass.X86.Point

/-!
# The ladder by calls of the point functions, on x86 (32-bit)

`ladderP L S` is `ladder L S` (`Impl/Weierstrass/X86.lean`) with the
doubling and the addition of an iteration as calls of
`vg_<curve>_point_double` and `vg_<curve>_point_add`
(`Impl/Weierstrass/X86/Point.lean`), for a curve whose points fit their fixed
slots and for which the functions are proven (coordinates of 3 to 6
words; P-521's do not fit, and its ladder inlines the complete addition), as
on 32-bit ARM
(`Impl/Weierstrass/Arm/LadderP.lean`):

1. `G`, `a` and `3b` are copied to the slots `Q`, `a` and `3b` of the point
   functions, once;
2. an iteration copies `R` to `P`, doubles it (`O = P + P`), copies the
   double to `P`, adds `G` (`O = P + Q`), and selects `R = O` if the bit is
   set, else `P`.

A call pushes the working space `edi` as the function's argument, in a frame
that `pop eax` releases, and then loads `edi` again from the caller's
argument holding it (at `[esp + arg]`), which no store changes, so that a
constant-time analysis knows it to be public; the point functions keep
`esi`, and a call uses 28 bytes of stack. Every address is still `edi`
plus a constant or a counter, or `esp` plus a constant.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86.Point

open VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open Spec.Weierstrass.Point (elemBytes aAt b3At oAt pAt qAt)

/-- The point of the fixed slots at `o`, for coordinates of `k` words. -/
def ptAt (k o : Nat) : Pt := ⟨o, o + elemBytes k, o + 2 * elemBytes k⟩

/-- `o = a`, points of `n`-word coordinates, through `eax`. -/
def copyPt (n : Nat) (o a : Pt) : List Instr :=
  copy (2 * n) o.x a.x ++ copy (2 * n) o.y a.y ++ copy (2 * n) o.z a.z

/-- A call of `vg_<curve>_point_double` (`dbl`) or `vg_<curve>_point_add` on
the working space at `edi`, which is then loaded again from the caller's
argument at `[esp + arg]`. -/
def ptCall (S : Spec.Weierstrass.Mont.Modulus) (dbl : Bool) (arg : Nat) : Prog isa :=
  .seq (.frame (.push [.edi]) (.call s!"vg_{S.curve}_point_{if dbl then "double" else "add"}" (fn S dbl))
    (.pop .eax 1)) (.block [.mov .edi (.mem (at_ .esp arg))])

/-- `G`, `a` and `3b` to the point functions' slots. -/
def ladderSetup (L : LadderCfg) : List Instr :=
  copyPt L.M.n (ptAt L.M.n (qAt L.M.n)) L.G ++ copy (2 * L.M.n) (aAt L.M.n) L.S.a ++
    copy (2 * L.M.n) (b3At L.M.n) L.S.b3

/-- One iteration, for the bit `t = esi - 1`: `P = R`, `O = P + P`, `P = O`,
`O = P + Q`, then `R = O` if bit `t` is set, else `P`. -/
def ladderPBody (L : LadderCfg) (S : Spec.Weierstrass.Mont.Modulus) (arg : Nat) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (.block (copyPt L.M.n (ptAt L.M.n (pAt L.M.n)) L.R)) <|
    .seq (ptCall S true arg) <|
    .seq (.block (copyPt L.M.n (ptAt L.M.n (pAt L.M.n)) (ptAt L.M.n (oAt L.M.n)))) <|
    .seq (ptCall S false arg) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R (ptAt L.M.n (pAt L.M.n)) (ptAt L.M.n (oAt L.M.n)) ++
      [testCounter])

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller, by calls of the point functions if the coordinates fit their slots,
else `ladder`. -/
def ladderP (L : LadderCfg) (S : Spec.Weierstrass.Mont.Modulus) (arg : Nat) : Prog isa :=
  if 3 ≤ L.M.n ∧ L.M.n ≤ 6 then
    .seq (.block (ladderSetup L ++ [.mov .esi (.imm (BitVec.ofNat 32 L.nbits))]))
      (.loop (ladderPBody L S arg) .ne)
  else ladder L S

end VG.Impl.Weierstrass.X86.Point
