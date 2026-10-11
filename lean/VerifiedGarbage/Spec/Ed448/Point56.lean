module

public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Spec.X448.Field56

/-!
# Ed448's point addition and doubling in radix `2^56`, as functions

**Trusted** (as every file in `Spec/`). The contracts of functions on points
of edwards448 in projective coordinates (`Point`), each coordinate an
element of `Spec/X448/Field56.lean` (eight limbs of 56 bits, the AArch64
code's representation), so that Ed448's verification on AArch64 can call
one copy of each instead of repeating it at every use:

* `vg_ed448_r56_point_add`: the sum `p + q`, by the specification's
  complete addition formula (`pointAdd`);
* `vg_ed448_r56_point_double`: `p` doubled, by RFC 8032 §5.2.4's doubling
  formulas (`pointDouble`).

They are not algorithms of a standard but the arithmetic Ed448 is built
from, in the representation that code keeps points in: what they compute is
stated on the coordinates as elements of `GF(p)`, `p = 2^448 - 2^224 - 1`.

A point is three coordinates, `X, Y, Z`, in consecutive slots of the
working space (`pointAt`): `p`, which the result replaces, in slots 3 to 5,
and `q` in slots 6 to 8. The functions keep `Field56.Bounded` (every limb of
every slot below `3·2^56 + 2^9`), and their results' limbs are below
`2^56 + 2^8` (`Field56.Res`). Doubling needs `p`'s `Z` with limbs below
that bound too, and 1 in slot 20; addition needs 0, with limbs below that
bound, in slot 19. Their temporaries are slots 10 to 18. On return those and
the functions' own bytes (`Field56.own`) are unspecified and may hold
intermediate values; every other byte of `ws` keeps its value but the
result's (`Field56.Keeps`).

Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

@[expose] public section

namespace VG.Spec.Ed448.Point56

open X448 (Fe)
open X448.Field56 (slotAt elemAt Bounded Res Keeps own)

/-- RFC 8032 §5.2.4's doubling formulas: `B = (X+Y)^2`, `C = X^2`,
`D = Y^2`, `E = C+D`, `H = Z^2`, `J = E-2H`, and `(X3, Y3, Z3) =
((B-E) J, E (C-D), E J)`. -/
def pointDouble (p : Point) : Point :=
  let b := (p.X + p.Y) * (p.X + p.Y)
  let c := p.X * p.X
  let dd := p.Y * p.Y
  let e := c + dd
  let h := p.Z * p.Z
  let j := e - (h + h)
  ⟨(b - e) * j, e * (c - dd), e * j⟩

/-- Where `p`, and the result, is: slots 3 to 5. -/
def pSlot : Nat := 3

/-- Where `q` is: slots 6 to 8. -/
def qSlot : Nat := 6

/-- The slot where addition needs 0. -/
def zeroSlot : Nat := 19

/-- The slot where doubling needs 1. -/
def oneSlot : Nat := 20

/-- The point in slots `n`, `n + 1` and `n + 2`. -/
def pointAt (m : Mem) (ws : Addr) (n : Nat) : Point :=
  ⟨elemAt m ws (slotAt n), elemAt m ws (slotAt (n + 1)), elemAt m ws (slotAt (n + 2))⟩

/-- What the functions change: the result, the temporaries (slots 10 to
18), and their own bytes. -/
def written : List (Nat × Nat) := (slotAt pSlot, slotAt (pSlot + 3)) :: (slotAt 10, slotAt 19) :: own

/-- The result's limbs are below `resBound`. -/
def ResPoint (m : Mem) (ws : Addr) : Prop := Res m ws pSlot ∧ Res m ws (pSlot + 1) ∧ Res m ws (pSlot + 2)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pointAdd`: with every slot `Bounded` and 0 in slot 19, with limbs below
`resBound`, the point in slots 3 to 5 becomes its sum with the point in
slots 6 to 8, with limbs below `resBound`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => Bounded m ws ∧ Res m ws zeroSlot ∧ elemAt m ws (slotAt zeroSlot) = 0)
    (post := fun ws m m' _ =>
      Bounded m' ws ∧ ResPoint m' ws ∧
        pointAt m' ws pSlot = pointAdd (pointAt m ws pSlot) (pointAt m ws qSlot) ∧
        Keeps ws written m m')
    (stack := stack)

/-- `pointDouble`: with every slot `Bounded`, the limbs of the point's `Z`
below `resBound` and 1 in slot 20, the point in slots 3 to 5 is doubled,
with limbs below `resBound`. -/
def doubleContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => Bounded m ws ∧ Res m ws (pSlot + 2) ∧ elemAt m ws (slotAt oneSlot) = 1)
    (post := fun ws m m' _ =>
      Bounded m' ws ∧ ResPoint m' ws ∧ pointAt m' ws pSlot = pointDouble (pointAt m ws pSlot) ∧
        Keeps ws written m m')
    (stack := stack)

/-- What both functions' documentation says of their elements. -/
def elemDoc : String :=
  "A point is three coordinates `X, Y, Z` in consecutive slots; slot `n` of `ws` is the first 64 \
    bytes from byte `64 + 128 n`, eight 64-bit little-endian words, least significant first, \
    each a limb: the number `Σ l_i 2^(56 i)`, standing for its residue modulo \
    `p = 2^448 - 2^224 - 1`, not necessarily reduced. The result's limbs are below \
    `2^56 + 2^8`. Every byte of `ws` but the result's, slots 10 to 18 (bytes 1344 to 2495) and \
    the function's own working space (bytes 3584 to 4735) keeps its value."

/-- What both functions require. -/
def safetyDoc (more : String) : List String :=
  [X448.Field56.boundedDoc, more,
    "Bytes 1344 to 2495 and 3584 to 4735 of `ws` are unspecified on return and may hold \
      intermediate values, which the caller must destroy if they are secret."]

/-- `vg_ed448_r56_point_add` on every target. -/
def addApi : Api where
  module := "ed448_r56"
  name := "vg_ed448_r56_point_add"
  sig := sig
  contracts := some fun A stack => addContract A stack
  summary := "Point addition on edwards448: replaces the point in slots 3 to 5 of the working \
    space `ws` (bytes 448 to 831) with its sum with the point in slots 6 to 8 (bytes 832 to \
    1215), by RFC 8032's complete addition formula in projective coordinates. " ++ elemDoc ++
    "\n\n\
    Contract: `addContract` of `VG.Spec.Ed448.Point56`. Constant time: only the pointer may \
    affect timing."
  safety := safetyDoc "Slot 19 of `ws` (byte 2496) must hold an element congruent to 0, with limbs below \
    `2^56 + 2^8`."

/-- `vg_ed448_r56_point_double` on every target. -/
def doubleApi : Api where
  module := "ed448_r56"
  name := "vg_ed448_r56_point_double"
  sig := sig
  contracts := some fun A stack => doubleContract A stack
  summary := "Point doubling on edwards448: replaces the point in slots 3 to 5 of the working \
    space `ws` (bytes 448 to 831) with its double, by RFC 8032's doubling formulas in projective \
    coordinates. " ++ elemDoc ++ "\n\n\
    Contract: `doubleContract` of `VG.Spec.Ed448.Point56`. Constant time: only the pointer may \
    affect timing."
  safety := safetyDoc "The limbs of slot 5 of `ws` (the point's `Z`, byte 704) must be below \
    `2^56 + 2^8`, and slot 20 (byte 2624) must hold an element congruent to 1."

end VG.Spec.Ed448.Point56
