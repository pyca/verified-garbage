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
# Montgomery arithmetic modulo secp256k1's `p` and `n`, as functions, on 32-bit ARM: verified

secp256k1's moduli, in four 64-bit words, are ones the functions support
(`ModOk`), so each of their functions meets the contract of its `Api`, as
the other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Spec.Weierstrass.Mont

theorem secp256k1p_ok : ModOk secp256k1p.k secp256k1p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem secp256k1n_ok : ModOk secp256k1n.k secp256k1n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem secp256k1p_mul_ct : ConstantTime isa (mulArm secp256k1p).pre (mulArm secp256k1p).pub (mulFn secp256k1p.k secp256k1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem secp256k1p_mul_verified : Verified Arm.target (mulFn secp256k1p.k secp256k1p.m) (secp256k1p.mulContract Arm.abi) :=
  mul_verified secp256k1p secp256k1p_ok (by decide) secp256k1p_mul_ct

theorem secp256k1p_add_ct : ConstantTime isa (addArm secp256k1p).pre (addArm secp256k1p).pub (addFn secp256k1p.k secp256k1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem secp256k1p_add_verified : Verified Arm.target (addFn secp256k1p.k secp256k1p.m) (secp256k1p.addContract Arm.abi) :=
  add_verified secp256k1p secp256k1p_ok (by decide) secp256k1p_add_ct

theorem secp256k1p_sub_ct : ConstantTime isa (subArm secp256k1p).pre (subArm secp256k1p).pub (subFn secp256k1p.k secp256k1p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem secp256k1p_sub_verified : Verified Arm.target (subFn secp256k1p.k secp256k1p.m) (secp256k1p.subContract Arm.abi) :=
  sub_verified secp256k1p secp256k1p_ok (by decide) secp256k1p_sub_ct

theorem secp256k1n_mul_ct : ConstantTime isa (mulArm secp256k1n).pre (mulArm secp256k1n).pub (mulFn secp256k1n.k secp256k1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem secp256k1n_mul_verified : Verified Arm.target (mulFn secp256k1n.k secp256k1n.m) (secp256k1n.mulContract Arm.abi) :=
  mul_verified secp256k1n secp256k1n_ok (by decide) secp256k1n_mul_ct

theorem secp256k1n_add_ct : ConstantTime isa (addArm secp256k1n).pre (addArm secp256k1n).pub (addFn secp256k1n.k secp256k1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem secp256k1n_add_verified : Verified Arm.target (addFn secp256k1n.k secp256k1n.m) (secp256k1n.addContract Arm.abi) :=
  add_verified secp256k1n secp256k1n_ok (by decide) secp256k1n_add_ct

theorem secp256k1n_sub_ct : ConstantTime isa (subArm secp256k1n).pre (subArm secp256k1n).pub (subFn secp256k1n.k secp256k1n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem secp256k1n_sub_verified : Verified Arm.target (subFn secp256k1n.k secp256k1n.m) (secp256k1n.subContract Arm.abi) :=
  sub_verified secp256k1n secp256k1n_ok (by decide) secp256k1n_sub_ct

end VG.Proof.Weierstrass.Arm.Mont
