module
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract

import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# Montgomery arithmetic modulo brainpoolP256r1's `p` and `n`, as functions, on 32-bit ARM: verified

brainpoolP256r1's moduli, in three 64-bit words, are ones the functions support
(`ModOk`), so each of their functions meets the contract of its `Api`, as
the other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Impl.Weierstrass.Mont

theorem brainpoolp256r1p_ok : ModOk brainpoolp256r1p.k brainpoolp256r1p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem brainpoolp256r1n_ok : ModOk brainpoolp256r1n.k brainpoolp256r1n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem brainpoolp256r1p_mul_ct : ConstantTime isa (mulArm brainpoolp256r1p).pre (mulArm brainpoolp256r1p).pub (mulFn brainpoolp256r1p.k brainpoolp256r1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1p_mul_verified : Verified Arm.target (mulFn brainpoolp256r1p.k brainpoolp256r1p.m) (brainpoolp256r1p.mulContract Arm.abi) :=
  mul_verified brainpoolp256r1p brainpoolp256r1p_ok (by decide) brainpoolp256r1p_mul_ct

theorem brainpoolp256r1p_add_ct : ConstantTime isa (addArm brainpoolp256r1p).pre (addArm brainpoolp256r1p).pub (addFn brainpoolp256r1p.k brainpoolp256r1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1p_add_verified : Verified Arm.target (addFn brainpoolp256r1p.k brainpoolp256r1p.m) (brainpoolp256r1p.addContract Arm.abi) :=
  add_verified brainpoolp256r1p brainpoolp256r1p_ok (by decide) brainpoolp256r1p_add_ct

theorem brainpoolp256r1p_sub_ct : ConstantTime isa (subArm brainpoolp256r1p).pre (subArm brainpoolp256r1p).pub (subFn brainpoolp256r1p.k brainpoolp256r1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1p_sub_verified : Verified Arm.target (subFn brainpoolp256r1p.k brainpoolp256r1p.m) (brainpoolp256r1p.subContract Arm.abi) :=
  sub_verified brainpoolp256r1p brainpoolp256r1p_ok (by decide) brainpoolp256r1p_sub_ct

theorem brainpoolp256r1n_mul_ct : ConstantTime isa (mulArm brainpoolp256r1n).pre (mulArm brainpoolp256r1n).pub (mulFn brainpoolp256r1n.k brainpoolp256r1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1n_mul_verified : Verified Arm.target (mulFn brainpoolp256r1n.k brainpoolp256r1n.m) (brainpoolp256r1n.mulContract Arm.abi) :=
  mul_verified brainpoolp256r1n brainpoolp256r1n_ok (by decide) brainpoolp256r1n_mul_ct

theorem brainpoolp256r1n_add_ct : ConstantTime isa (addArm brainpoolp256r1n).pre (addArm brainpoolp256r1n).pub (addFn brainpoolp256r1n.k brainpoolp256r1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1n_add_verified : Verified Arm.target (addFn brainpoolp256r1n.k brainpoolp256r1n.m) (brainpoolp256r1n.addContract Arm.abi) :=
  add_verified brainpoolp256r1n brainpoolp256r1n_ok (by decide) brainpoolp256r1n_add_ct

theorem brainpoolp256r1n_sub_ct : ConstantTime isa (subArm brainpoolp256r1n).pre (subArm brainpoolp256r1n).pub (subFn brainpoolp256r1n.k brainpoolp256r1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp256r1n_sub_verified : Verified Arm.target (subFn brainpoolp256r1n.k brainpoolp256r1n.m) (brainpoolp256r1n.subContract Arm.abi) :=
  sub_verified brainpoolp256r1n brainpoolp256r1n_ok (by decide) brainpoolp256r1n_sub_ct

end VG.Proof.Weierstrass.Arm.Mont
