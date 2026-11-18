module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.State
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math`, which this module and modules that import it used -/

section

/-! Curve-independent radix-four group identities, shared with Brainpool. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
export VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
  (pair pair_curve pair_add pair_zero shift_radix stage at_step at_zero at_top
   pair_generator pair_peer previous previous_lt table_step point_comm)
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

end

end

/-! Full ECDSA verification correctness with the joint public multiplier. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem verify_ok (hc : BaseCfgOk cfg) (hC : Law C) {s₀ : State} (hp : FrontPre cfg s₀) :
    WP isa verify s₀ fun s' => (∀ r ∈ Cfg.saved.map Prod.fst,s'.gpr r=s₀.gpr r) ∧ VPost cfg s₀ s' :=
  JointKit.verifyWith_ok (fun hP hM hrep => points_ok hc hC hP hM hrep) hc hC hp
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
