module

public import VerifiedGarbage.Proof.Ct.Common
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ct
open VG

theorem result32 (d : Byte) :
    ((d.setWidth 32 - 1) >>> 31) = if d = 0 then 1 else 0 := by
  have h : ∀ d : Byte, ((d.setWidth 32 - 1) >>> 31) =
      if d = 0 then 1 else 0 := by decide +kernel
  exact h d
end VG.Proof.Ct
