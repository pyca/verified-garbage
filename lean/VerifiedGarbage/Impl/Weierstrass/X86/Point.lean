module

public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Spec.Weierstrass.Point

/-!
# Complete point addition and doubling as functions, on x86 (32-bit)

`vg_<curve>_point_add(ws)` and `vg_<curve>_point_double(ws)`
(`Spec/Weierstrass/Point.lean`; cdecl: `ws` at `[esp + 4]`) for a curve whose
coordinates are `k` 64-bit words: the complete addition `rcb`
(`Impl/Weierstrass/Slots.lean`) of the points at fixed offsets, as calls of
the Montgomery functions of the curve's prime
(`Impl/Weierstrass/X86/Mont.lean`):

1. `edi` is saved in the functions' own working space, and takes `ws`;
2. each field operation of `rcb` is a call of its function on `edi` and
   the offsets of its three operands (`Mont.callOp`): the Montgomery
   functions keep `edi`, and a constant-time analysis knows it to be public
   across their calls;
3. `edi` is restored, and the function returns.

The functions write no register but `eax`, `ecx`, `edx` and (restoring it)
`edi`, so a constant-time analysis of a caller's code knows `esi` to be
public across a call. It does not know the restored `edi` to be (the
functions store at offsets, which makes it forget memory), so a caller
whose working space is in `edi` loads it again from its own arguments
(`ladderP`, `Impl/Weierstrass/X86/LadderP.lean`). The operations name their slots by number (`ids`), as on
32-bit ARM (`Impl/Weierstrass/Arm/Point.lean`): every address is `ws` or
`esp` plus a constant, so only the pointer may affect timing. A call's
frame and return address use 20 bytes of stack.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86.Point

open VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open Spec.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- A call of the function `f`, whose code is `body`, on the working space at
`edi` and the offsets of the slots `o`, `a` and `b` (`enc`): `callOp`. -/
def callB (enc : Nat → Nat) (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  Mont.callOp f body (enc o) (enc a) (enc b)

/-- The code of a field operation modulo `S` on the slots `enc` gives. -/
def opCodeB (enc : Nat → Nat) (S : Spec.Weierstrass.Mont.Modulus) : FOp → Prog isa
  | .mul o a b => callB enc (S.fn "mul") (Mont.mulFn S.k S.m) o a b
  | .add o a b => callB enc (S.fn "add") (Mont.addFn S.k S.m) o a b
  | .sub o a b => callB enc (S.fn "sub") (Mont.subFn S.k S.m) o a b

/-- A straight-line sequence of field operations on the slots `enc` gives. -/
def fprogB (enc : Nat → Nat) (S : Spec.Weierstrass.Mont.Modulus) (ops : List FOp) : Prog isa :=
  progs (ops.map (opCodeB enc S))

/-! ## The slots, by number -/

/-- The points: `O`'s coordinates are slots 0–2, the first operand's 3–5 and
the second's 6–8. -/
def oId : Pt := ⟨0, 1, 2⟩
def pId : Pt := ⟨3, 4, 5⟩
def qId : Pt := ⟨6, 7, 8⟩

/-- `a`, `3b` and the six temporaries: slots 9–16. -/
def sId : RcbSlots := ⟨9, 10, 11, 12, 13, 14, 15, 16⟩

/-- Where `edi` is saved: the start of the own working space. -/
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

/-- `edi` saved through the argument `ws`, then `edi = ws`. -/
def entry (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax (saveAt k)) .edi, .mov .edi (.reg .eax)]

/-- `edi` restored. -/
def restore (k : Nat) : List Instr := [.mov .edi (.mem (at_ .edi (saveAt k)))]

/-- The function's code, calling the Montgomery functions of `S`: `O = P + Q`,
or `P + P` if `dbl`. -/
def fn (S : Spec.Weierstrass.Mont.Modulus) (dbl : Bool) : Prog isa :=
  .seq (.block (entry S.k)) <| .seq (fprogB (enc S.k dbl) S (rcb sId pId qId oId)) <| .block (restore S.k)

/-- The curve's prime as a modulus of `Spec/Weierstrass/Mont.lean`, whose
functions (`vg_<curve>_<op>_mod_p`) the point functions call. -/
abbrev modP (C : Spec.Weierstrass.Point.Curve) : Spec.Weierstrass.Mont.Modulus :=
  { curve := C.curve, which := "p", m := C.p, k := C.k, desc := C.desc }

/-- `vg_<curve>_point_add`. -/
def pointAdd (C : Spec.Weierstrass.Point.Curve) : Prog isa := fn (modP C) false

/-- `vg_<curve>_point_double`. -/
def pointDouble (C : Spec.Weierstrass.Point.Curve) : Prog isa := fn (modP C) true

end VG.Impl.Weierstrass.X86.Point
