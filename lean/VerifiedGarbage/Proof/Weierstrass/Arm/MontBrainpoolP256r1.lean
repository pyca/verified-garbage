module
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract

import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.Arm.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Row
meta import VerifiedGarbage.Proof.Mont.Arm.Step
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Spec.X25519

/-!
# Montgomery arithmetic modulo brainpoolP256r1's `p` and `n`, as functions, on 32-bit ARM: verified

brainpoolP256r1's moduli, in three 64-bit words, are ones the functions support
(`ModOk`), so each of their functions meets the contract of its `Api`, as
the other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Spec.Weierstrass.Mont

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
