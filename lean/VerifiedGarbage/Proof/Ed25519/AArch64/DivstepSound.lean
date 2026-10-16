module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
import VerifiedGarbage.Proof.Ed25519.Group.Extended
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps is sound modulo `p = 2²⁵⁵ - 19`

Untrusted: everything here is checked by Lean. The short Weierstrass curves'
inversion (`InvCfg.inv`) is proven for any prime modulus (`invSound_of_toM`);
`p` is prime (`Ed25519.prime_field`). This module alone imports the algebra
those take.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG.Proof.Weierstrass.AArch64

theorem p_prime : Nat.Prime VG.Spec.X25519.P := VG.Proof.Ed25519.prime_field

theorem invSound : InvSound VG.Spec.X25519.P :=
  invSound_of_toM p_prime (VG.Proof.Weierstrass.invToM_of_prime p_prime)

instance sound : Sound := ⟨invSound⟩

end VG.Proof.Ed25519.AArch64.Divstep
