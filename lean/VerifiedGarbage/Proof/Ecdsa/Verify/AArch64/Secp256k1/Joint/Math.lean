module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! Curve-independent radix-four group identities, shared with Brainpool. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
export VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
  (pair pair_curve pair_add pair_zero shift_radix stage at_step at_zero at_top
   pair_generator pair_peer previous previous_lt table_step point_comm)
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
