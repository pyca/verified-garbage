module

public import VerifiedGarbage.Spec.Rc2

/-!
# RC2: PITABLE as a table of constants

Implementations that read PITABLE (RFC 2268 §2) from memory, by scanning it
whole, read it from the static `VG_RC2_PITABLE`: its 256 bytes, in order, as
32 little-endian quadwords.
-/

@[expose] public section

namespace VG.Impl.Rc2

/-- Quadword `q` of the table: PITABLE's bytes `8 q … 8 q + 7`, little-endian. -/
def piQuad (q : Nat) : BitVec 64 :=
  (List.range 8).foldr (fun j acc => acc ||| (Spec.Rc2.piTable.getD (8 * q + j) 0).setWidth 64 <<< (8 * j)) 0

/-- PITABLE as 32 quadwords. -/
def piQuads : List (BitVec 64) := (List.range 32).map piQuad

def piSym : String := "VG_RC2_PITABLE"

/-- The tables key expansion reads. -/
def piConsts : List (String × List (BitVec 64)) := [(piSym, piQuads)]

end VG.Impl.Rc2
