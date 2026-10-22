module

public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Proof.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-224's square-root certificate

`p - 1 = (2^128 - 1) * 2^96`. Eleven is a quadratic nonresidue;
the kernel checks its Euler criterion directly with the specification's
binary exponentiation. No Rust constants or external computation are used.
-/

@[expose] public section

namespace VG.Proof.P224

open Spec.Weierstrass VG.Impl.EcKey.Compressed

private theorem nonresidue :
    pow (Fin.ofNat Spec.P224.curve.p 11) ((Spec.P224.curve.p - 1) / 2) = -1 := by
  decide +kernel

/-- The P-224 candidate succeeds for every square, including zero. -/
theorem root_square (hL : Weierstrass.Law Spec.P224.curve)
    (a : Fe Spec.P224.curve) (ha : ∃ y : Fe Spec.P224.curve, y * y = a) :
    let r := rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96
      (Fin.ofNat Spec.P224.curve.p 11)
    r * r = a := by
  apply Weierstrass.rootTonelli_square hL (by decide +kernel)
  · decide
  · decide +kernel
  · decide +kernel
  · rw [show (Spec.P224.curve.p - 1) / 2 ^ 96 * 2 ^ (96 - 1) =
        (Spec.P224.curve.p - 1) / 2 by decide +kernel,
      nonresidue]
  · exact ha

/-- The same proof-only interface as the other curves, with P-224's own
square-root method. -/
theorem rootFacts (hL : Weierstrass.Law Spec.P224.curve) :
    EcKey.Compressed.RootFacts (fun a : Fe Spec.P224.curve =>
    rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96
      (Fin.ofNat Spec.P224.curve.p 11)) := by
  exact ⟨root_square hL, Weierstrass.square_roots_eq_or_neg hL⟩

end VG.Proof.P224
