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

/-!
# Montgomery arithmetic modulo brainpoolP384r1's `p` and `n`, as functions, on 32-bit ARM: verified

brainpoolP384r1's moduli, in six 64-bit words, are ones the functions support
(`ModOk`), so each of their functions meets the contract of its `Api`, as
the other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Spec.Weierstrass.Mont

theorem brainpoolp384r1p_ok : ModOk brainpoolp384r1p.k brainpoolp384r1p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem brainpoolp384r1n_ok : ModOk brainpoolp384r1n.k brainpoolp384r1n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem brainpoolp384r1p_mul_ct : ConstantTime isa (mulArm brainpoolp384r1p).pre (mulArm brainpoolp384r1p).pub (mulFn brainpoolp384r1p.k brainpoolp384r1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1p_mul_verified : Verified Arm.target (mulFn brainpoolp384r1p.k brainpoolp384r1p.m) (brainpoolp384r1p.mulContract Arm.abi) :=
  mul_verified brainpoolp384r1p brainpoolp384r1p_ok (by decide) brainpoolp384r1p_mul_ct

theorem brainpoolp384r1p_add_ct : ConstantTime isa (addArm brainpoolp384r1p).pre (addArm brainpoolp384r1p).pub (addFn brainpoolp384r1p.k brainpoolp384r1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1p_add_verified : Verified Arm.target (addFn brainpoolp384r1p.k brainpoolp384r1p.m) (brainpoolp384r1p.addContract Arm.abi) :=
  add_verified brainpoolp384r1p brainpoolp384r1p_ok (by decide) brainpoolp384r1p_add_ct

theorem brainpoolp384r1p_sub_ct : ConstantTime isa (subArm brainpoolp384r1p).pre (subArm brainpoolp384r1p).pub (subFn brainpoolp384r1p.k brainpoolp384r1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1p_sub_verified : Verified Arm.target (subFn brainpoolp384r1p.k brainpoolp384r1p.m) (brainpoolp384r1p.subContract Arm.abi) :=
  sub_verified brainpoolp384r1p brainpoolp384r1p_ok (by decide) brainpoolp384r1p_sub_ct

theorem brainpoolp384r1n_mul_ct : ConstantTime isa (mulArm brainpoolp384r1n).pre (mulArm brainpoolp384r1n).pub (mulFn brainpoolp384r1n.k brainpoolp384r1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1n_mul_verified : Verified Arm.target (mulFn brainpoolp384r1n.k brainpoolp384r1n.m) (brainpoolp384r1n.mulContract Arm.abi) :=
  mul_verified brainpoolp384r1n brainpoolp384r1n_ok (by decide) brainpoolp384r1n_mul_ct

theorem brainpoolp384r1n_add_ct : ConstantTime isa (addArm brainpoolp384r1n).pre (addArm brainpoolp384r1n).pub (addFn brainpoolp384r1n.k brainpoolp384r1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1n_add_verified : Verified Arm.target (addFn brainpoolp384r1n.k brainpoolp384r1n.m) (brainpoolp384r1n.addContract Arm.abi) :=
  add_verified brainpoolp384r1n brainpoolp384r1n_ok (by decide) brainpoolp384r1n_add_ct

theorem brainpoolp384r1n_sub_ct : ConstantTime isa (subArm brainpoolp384r1n).pre (subArm brainpoolp384r1n).pub (subFn brainpoolp384r1n.k brainpoolp384r1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem brainpoolp384r1n_sub_verified : Verified Arm.target (subFn brainpoolp384r1n.k brainpoolp384r1n.m) (brainpoolp384r1n.subContract Arm.abi) :=
  sub_verified brainpoolp384r1n brainpoolp384r1n_ok (by decide) brainpoolp384r1n_sub_ct

end VG.Proof.Weierstrass.Arm.Mont
