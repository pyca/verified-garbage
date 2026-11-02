module

public import VerifiedGarbage.Impl.EcKey.Compressed.RootTable
public import VerifiedGarbage.Proof.EcKey.Compressed.Root
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.RootTable
import VerifiedGarbage.Proof.Weierstrass.Sqrt

/-!
# P-224's square root by a table (`root224`)

`p - 1 = (2^128 - 1) 16^24`; `c = 11^q` has `c^(2^95) = -1`, and the 16
entries `c^(e 16^23)` of the table's last row are different: the kernel
checks both with the specification's binary exponentiation. Then
`rootTable_square` (`Proof/Weierstrass/RootTable.lean`) gives a root of every
square.
-/

-- separate module: its kernel checks of the constants, apart from the code's proofs

@[expose] public section

namespace VG.Proof.P224

open Spec.Weierstrass VG.Impl.EcKey.Compressed VG.Proof.Weierstrass

theorem c224_pow : c224 ^ (2 ^ (4 * 24 - 1)) = -1 := by
  rw [← pow_eq_npow]; decide +kernel

theorem tbl224_eq (m d : Nat) : tbl224 m d = c224 ^ (d * 16 ^ m) := pow_eq_npow _ _

theorem tbl224_vals : ∀ e < 16, ∀ e' < 16, (tbl224 23 e).val = (tbl224 23 e').val → e = e' := by
  decide +kernel

theorem tbl224_inj (e e' : Nat) (he : e < 16) (he' : e' < 16) (h : tbl224 23 e = tbl224 23 e') : e = e' :=
  tbl224_vals e he e' he' (congrArg Fin.val h)

/-- The candidate root of a square is a root. -/
theorem root224_square (hL : Weierstrass.Law Spec.P224.curve) (a : Fe Spec.P224.curve)
    (ha : ∃ y : Fe Spec.P224.curve, y * y = a) : root224 a * root224 a = a :=
  rootTable_square hL (by decide) (by decide) (by decide) (by decide) c224_pow tbl224_eq tbl224_inj a ha

/-- The proof-only interface of the curves' roots, for `root224`. -/
theorem rootFacts224 (hL : Weierstrass.Law Spec.P224.curve) : EcKey.Compressed.RootFacts root224 :=
  ⟨root224_square hL, square_roots_eq_or_neg hL⟩

end VG.Proof.P224
