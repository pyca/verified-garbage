module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Call
public import VerifiedGarbage.Impl.Weierstrass.Rcb0
public import VerifiedGarbage.Impl.Weierstrass.Layout.Point

/-!
# Complete point addition and doubling as functions, on PPC64LE

`vg_<curve>_point_add(ws)` and `vg_<curve>_point_double(ws)`
(`Proof/Weierstrass/PointContract.lean`; ELFv2: `ws` in `r3`) for a curve whose
coordinates are `k` 64-bit words: the complete addition `rcb`
(`Impl/Weierstrass/Slots.lean`) of the points at fixed offsets, as calls of
the Montgomery functions of the curve's prime
(`Impl/Weierstrass/PPC64LE/Mont.lean`), as on 32-bit ARM
(`Impl/Weierstrass/Arm/Point.lean`):

1. the link register, which the calls change, is saved in the functions'
   own working space (through `r0`);
2. each field operation of `rcb` loads the offsets of its three operands
   into `r4`–`r6` (`li`) and calls its function, which leaves `r3 = ws`;
3. the link register is restored, and the function returns.

The functions write only `r0` and `r4`–`r12` (their callees' registers), so
that a caller keeps what it holds in `r3` and `r14`–`r31`, and a
constant-time analysis of a caller's code knows those to be as public across
a call as before it. The operations name their slots by number (`ids`): the
points' coordinates, the constants and the six temporaries, which `enc`
turns into offsets; the doubling reads `P` as both operands. Every address
is `ws` plus a constant, so only the pointer may affect timing. The
functions use no stack.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE.Point

open VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- The code of a field operation modulo `S` on slots named by number, each
slot `x` at offset `σ x`. -/
def opCodeR (σ : Nat → Nat) (S : Impl.Weierstrass.Mont.Modulus) : FOp → Prog isa
  | .mul o a b => mulCall S (σ o) (σ a) (σ b)
  | .add o a b => addCall S (σ o) (σ a) (σ b)
  | .sub o a b => subCall S (σ o) (σ a) (σ b)

/-- The field operations `ops` on slots named by number. -/
def fprogR (σ : Nat → Nat) (S : Impl.Weierstrass.Mont.Modulus) (ops : List FOp) : Prog isa :=
  progs (ops.map (opCodeR σ S))

/-! ## The slots, by number -/

/-- The points: `O`'s coordinates are slots 0–2, the first operand's 3–5 and
the second's 6–8. -/
def oId : Pt := ⟨0, 1, 2⟩
def pId : Pt := ⟨3, 4, 5⟩
def qId : Pt := ⟨6, 7, 8⟩

/-- `a`, `3b` and the six temporaries: slots 9–16. -/
def sId : RcbSlots := ⟨9, 10, 11, 12, 13, 14, 15, 16⟩

/-- Where `lr` is saved: the start of the own working space. -/
def saveAt (k : Nat) : Nat := ownAt k

/-- Where temporary `i` is: after the 64 bytes for saved registers. -/
def tmpAt (k i : Nat) : Nat := ownAt k + 64 + elemBytes k * i

/-- The offset of each slot, for coordinates of `k` words; the second
operand is `P` if `dbl`, else `Q`. -/
def enc (k : Nat) (dbl : Bool) (i : Nat) : Nat :=
  if i < 3 then oAt k + elemBytes k * i
  else if i < 6 then pAt k + elemBytes k * (i - 3)
  else if i < 9 then (if dbl then pAt k else qAt k) + elemBytes k * (i - 6)
  else if i = 9 then aAt k
  else if i = 10 then b3At k
  else tmpAt k (i - 11)

/-- `lr` saved, through `r0`. -/
def entry (k : Nat) : List Instr := [.mflr .r0, .store .d .r0 .r3 (saveAt k)]

/-- `lr` restored, through `r0`. -/
def restore (k : Nat) : List Instr := [.load .d .r0 .r3 (saveAt k), .mtlr .r0]

/-- A function computing the field operations `ops` on the slots, calling the
Montgomery functions of `S` (the second operand's slots `P`'s if `dbl`). -/
def fnOps (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) (ops : List FOp) : Prog isa :=
  .seq (.block (entry S.k)) <| .seq (fprogR (enc S.k dbl) S ops) <| .block (restore S.k)

/-- The function's code, calling the Montgomery functions of `S`: `O = P + Q`,
or `P + P` if `dbl`. -/
def fn (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) : Prog isa :=
  fnOps S dbl (rcb sId pId qId oId)

/-- The formulas for `a = 0`: Algorithm 9 doubles (`dbl`), Algorithm 8 adds. -/
def ops0 (dbl : Bool) : List FOp := if dbl then dbl0 sId pId oId else rcb0m sId pId qId oId

/-- `O = P + P` (`dbl`) or `P + Q` by the formulas for `a = 0`. -/
def fn0 (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) : Prog isa := fnOps S dbl (ops0 dbl)

/-- The curve's prime as a modulus of `Proof/Weierstrass/MontContract.lean`, whose
functions (`vg_<curve>_<op>_mod_p`) the point functions call. -/
abbrev modP (C : Impl.Weierstrass.Point.Curve) : Impl.Weierstrass.Mont.Modulus :=
  { curve := C.curve, which := "p", m := C.p, k := C.k, desc := C.desc }

/-- `vg_<curve>_point_add`. -/
def pointAdd (C : Impl.Weierstrass.Point.Curve) : Prog isa := fn (modP C) false

/-- `vg_<curve>_point_double`. -/
def pointDouble (C : Impl.Weierstrass.Point.Curve) : Prog isa := fn (modP C) true

/-- `vg_<curve>_point_a0_double`: `O = P + P` by Algorithm 9. -/
def pointDouble0 (C : Impl.Weierstrass.Point.Curve) : Prog isa := fn0 (modP C) true

/-- `vg_<curve>_point_a0_add_affine`: `O = P + Q` by Algorithm 8. -/
def pointAdd0m (C : Impl.Weierstrass.Point.Curve) : Prog isa := fn0 (modP C) false

end VG.Impl.Weierstrass.PPC64LE.Point
