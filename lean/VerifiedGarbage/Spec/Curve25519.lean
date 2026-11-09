module

public import VerifiedGarbage.TCB.Mem

/-! # The field shared by Ed25519 and the X25519 implementation

**Trusted.** Arithmetic modulo 2²⁵⁵ - 19, used by the Ed25519 specification.
X25519's public contracts use Wychelean; its implementation model also uses
this finite representation of the field.
-/

@[expose] public section

namespace VG.Spec.X25519

/-- The prime `p = 2²⁵⁵ - 19` (§4.1). -/
def P : Nat := 2 ^ 255 - 19

instance : NeZero P := ⟨by decide⟩

/-- An element of `GF(p)`. -/
abbrev Fe := Fin P

/-- `a ^ e` in `GF(p)`: `e` factors of `a` (`1` if `e = 0`), computed by
square-and-multiply from `a ^ e = (a · a) ^ ⌊e / 2⌋ · a ^ (e mod 2)`. -/
def pow (a : Fe) (e : Nat) : Fe :=
  if e = 0 then 1 else
  let r := pow (a * a) (e / 2)
  if e % 2 = 0 then r else a * r
termination_by e
decreasing_by omega


end VG.Spec.X25519
