import VerifiedGarbage.Impl.Mont.Mod

/-!
# Short Weierstrass curves: field programs on slots, on any target

What the code of each target (`Impl/Weierstrass/<Target>.lean`) computes,
independently of its instructions. Field elements are in Montgomery form
in slots of the working space (byte offsets); a point is three slots,
projective coordinates `(X : Y : Z)`.

* `FOp`: a field operation on slots, and `rcb`, the sum of two points by the
  complete formulas of Renes, Costello and Batina (Algorithm 1, any `a`), in
  their 40 steps;
* `LadderCfg`, `PowCfg`, `CombCfg`: the slots and tables of bits that scalar
  multiplication, powers and the fixed-base comb use.
-/

namespace VG.Impl.Weierstrass

open VG.Impl.Mont

/-- A field operation on slots (byte offsets of the working space). -/
inductive FOp
  | mul (o a b : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)

/-- A point: the slots of its three coordinates. -/
structure Pt where
  x : Nat
  y : Nat
  z : Nat

/-- The slots the complete addition uses: the curve's `a` and `3b`, and six
temporaries. -/
structure RcbSlots where
  a : Nat
  b3 : Nat
  t0 : Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  t4 : Nat
  t5 : Nat

/-- `o = p + q` (Algorithm 1 of Renes, Costello and Batina, in its stated
order; `o`'s slots are written as temporaries too, so they must be apart
from `p`'s and `q`'s). -/
def rcb (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.x q.x, .mul S.t1 p.y q.y, .mul S.t2 p.z q.z,
    .add S.t3 p.x p.y, .add S.t4 q.x q.y, .mul S.t3 S.t3 S.t4,
    .add S.t4 S.t0 S.t1, .sub S.t3 S.t3 S.t4, .add S.t4 p.x p.z,
    .add S.t5 q.x q.z, .mul S.t4 S.t4 S.t5, .add S.t5 S.t0 S.t2,
    .sub S.t4 S.t4 S.t5, .add S.t5 p.y p.z, .add o.x q.y q.z,
    .mul S.t5 S.t5 o.x, .add o.x S.t1 S.t2, .sub S.t5 S.t5 o.x,
    .mul o.z S.a S.t4, .mul o.x S.b3 S.t2, .add o.z o.x o.z,
    .sub o.x S.t1 o.z, .add o.z S.t1 o.z, .mul o.y o.x o.z,
    .add S.t1 S.t0 S.t0, .add S.t1 S.t1 S.t0, .mul S.t2 S.a S.t2,
    .mul S.t4 S.b3 S.t4, .add S.t1 S.t1 S.t2, .sub S.t2 S.t0 S.t2,
    .mul S.t2 S.a S.t2, .add S.t4 S.t4 S.t2, .mul S.t0 S.t1 S.t4,
    .add o.y o.y S.t0, .mul S.t0 S.t5 S.t4, .mul o.x S.t3 o.x,
    .sub o.x o.x S.t0, .mul S.t0 S.t3 S.t1, .mul o.z S.t5 o.z,
    .add o.z o.z S.t0]

/-- What scalar multiplication needs: the field, the slots of `G` and of the
points, the slots of the complete addition, and the table of the scalar's
bits (byte `t` is bit `t`), with `nbits` bits. -/
structure LadderCfg where
  M : Mod
  S : RcbSlots
  G : Pt
  R : Pt
  D : Pt
  T : Pt
  bits : Nat
  nbits : Nat

/-- What a power needs: the modulus, the slots of the accumulator, of a
temporary, of the base and of `R mod m` (Montgomery's one), and the table of
the exponent's bits, with `nbits` bits. -/
structure PowCfg where
  M : Mod
  acc : Nat
  tmp : Nat
  base : Nat
  one : Nat
  bits : Nat
  nbits : Nat

/-- What the comb needs: the field, the complete addition's slots, the
accumulator `A` (the result), the slots of the selected entry `E` and of the
sum `D`, a slot for `-y` and one holding zero, the scalar's table of bits,
the tables (`tbl[j][m - 1]` is the Montgomery form of `[m 16^j]P`'s `(x, y)`),
the start `[c]P` (Montgomery `(x, y)`) and `R mod p`. -/
structure CombCfg where
  M : Mod
  S : RcbSlots
  A : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  tbl : List (List (Nat × Nat))
  start : Nat × Nat
  one : Nat

/-- The number of the comb's tables (and of digits). -/
def CombCfg.J (K : CombCfg) : Nat := K.tbl.length

end VG.Impl.Weierstrass
