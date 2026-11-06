module

import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI

/-! # The run-time width multiplication's final selection

`select_mod`: selecting `T - M` when it did not borrow, and `T` otherwise,
gives `T mod M`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG.Proof.Mont

/-- The value selected into the result is `T mod M`. -/
theorem select_mod {Tl D top X M : Nat} {c : Bool} (hX : M < X) (hD : D < X) (hV : Tl + X * top < 2 * M)
    (he : D + M = Tl + X * c.toNat) :
    (if !(decide (top < c.toNat)) then D else Tl) = (Tl + X * top) % M := by
  rw [← csub_arith hX hD hV he]
  by_cases h : top < c.toNat <;> simp [h]

end VG.Proof.Mont.X86.Rt
