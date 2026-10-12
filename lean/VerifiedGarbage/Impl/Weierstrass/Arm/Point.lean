module

public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Spec.Weierstrass.Point

/-!
# Complete point addition and doubling as functions, on 32-bit ARM

`vg_<curve>_point_add(ws)` and `vg_<curve>_point_double(ws)`
(`Spec/Weierstrass/Point.lean`; AAPCS: `ws` in `r0`) for a curve whose
coordinates are `k` 64-bit words: the complete addition `rcb`
(`Impl/Weierstrass/Slots.lean`) of the points at fixed offsets, as calls of
the Montgomery functions of the curve's prime
(`Impl/Weierstrass/Arm/Mont.lean`):

1. `r12` takes `ws`, and `lr` is saved in the functions' own working space;
2. each field operation of `rcb` loads the offsets of its three operands
   into `r1`–`r3` (`movw`) and calls its function with `r0 = r12`; the
   functions leave `r12 = ws`;
3. `lr` is restored, and the function returns.

The functions write no other register (the Montgomery functions keep
`r4`–`r11`), so that a caller keeps what it holds in them, and a
constant-time analysis of a caller's code knows `r10` and `r11` to be
public across a call, as across a call of a Montgomery function. The
operations name their slots by number (`ids`): the points' coordinates, the
constants and the six temporaries, which `enc` turns into offsets; the
doubling reads `P` as both operands. Every address is `ws` plus a constant,
so only the pointer may affect timing. The functions use no stack.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Arm.Point

open VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open Spec.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- A call of the function `f`, whose code is `body`, on the working space at
`r12` and the offsets of the slots `o`, `a` and `b` (`enc`). -/
def callR (enc : Nat → Nat) (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r12), .movw .r1 (BitVec.ofNat 16 (enc o)), .movw .r2 (BitVec.ofNat 16 (enc a)),
    .movw .r3 (BitVec.ofNat 16 (enc b))]) (.call f body)

/-- The code of a field operation modulo `S` on the slots `enc` gives. -/
def opCodeR (enc : Nat → Nat) (S : Spec.Weierstrass.Mont.Modulus) : FOp → Prog isa
  | .mul o a b => callR enc (S.fn "mul") (Mont.mulFn S.k S.m) o a b
  | .add o a b => callR enc (S.fn "add") (Mont.addFn S.k S.m) o a b
  | .sub o a b => callR enc (S.fn "sub") (Mont.subFn S.k S.m) o a b

/-- A straight-line sequence of field operations on the slots `enc` gives. -/
def fprogR (enc : Nat → Nat) (S : Spec.Weierstrass.Mont.Modulus) (ops : List FOp) : Prog isa :=
  progs (ops.map (opCodeR enc S))

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

/-- `r12 = ws`, and `lr` saved through it. -/
def entry (k : Nat) : List Instr := [.mov .r12 (.reg .r0), .str .lr .r12 (saveAt k)]

/-- `lr` restored. -/
def restore (k : Nat) : List Instr := [.ldr .lr .r12 (saveAt k)]

/-- The function's code, calling the Montgomery functions of `S`: `O = P + Q`,
or `P + P` if `dbl`. -/
def fn (S : Spec.Weierstrass.Mont.Modulus) (dbl : Bool) : Prog isa :=
  .seq (.block (entry S.k)) <| .seq (fprogR (enc S.k dbl) S (rcb sId pId qId oId)) <| .block (restore S.k)

/-- The curve's prime as a modulus of `Spec/Weierstrass/Mont.lean`, whose
functions (`vg_<curve>_<op>_mod_p`) the point functions call. -/
abbrev modP (C : Spec.Weierstrass.Point.Curve) : Spec.Weierstrass.Mont.Modulus :=
  { curve := C.curve, which := "p", m := C.p, k := C.k, desc := C.desc }

/-- `vg_<curve>_point_add`. -/
def pointAdd (C : Spec.Weierstrass.Point.Curve) : Prog isa := fn (modP C) false

/-- `vg_<curve>_point_double`. -/
def pointDouble (C : Spec.Weierstrass.Point.Curve) : Prog isa := fn (modP C) true

end VG.Impl.Weierstrass.Arm.Point
