module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo P224's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem p224p_mul_ct : ConstantTime isa (mulPPC p224p).pre (mulPPC p224p).pub (mulFn p224p.k p224p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224p_mul_verified : Verified PPC64LE.target (mulFn p224p.k p224p.m) (p224p.mulContract PPC64LE.abi) :=
  mul_verified p224p p224p_ok p224p_mul_ct

theorem p224p_add_ct : ConstantTime isa (addPPC p224p).pre (addPPC p224p).pub (addFn p224p.k p224p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224p_add_verified : Verified PPC64LE.target (addFn p224p.k p224p.m) (p224p.addContract PPC64LE.abi) :=
  add_verified p224p p224p_ok p224p_add_ct

theorem p224p_sub_ct : ConstantTime isa (subPPC p224p).pre (subPPC p224p).pub (subFn p224p.k p224p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224p_sub_verified : Verified PPC64LE.target (subFn p224p.k p224p.m) (p224p.subContract PPC64LE.abi) :=
  sub_verified p224p p224p_ok p224p_sub_ct

theorem p224n_mul_ct : ConstantTime isa (mulPPC p224n).pre (mulPPC p224n).pub (mulFn p224n.k p224n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224n_mul_verified : Verified PPC64LE.target (mulFn p224n.k p224n.m) (p224n.mulContract PPC64LE.abi) :=
  mul_verified p224n p224n_ok p224n_mul_ct

theorem p224n_add_ct : ConstantTime isa (addPPC p224n).pre (addPPC p224n).pub (addFn p224n.k p224n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224n_add_verified : Verified PPC64LE.target (addFn p224n.k p224n.m) (p224n.addContract PPC64LE.abi) :=
  add_verified p224n p224n_ok p224n_add_ct

theorem p224n_sub_ct : ConstantTime isa (subPPC p224n).pre (subPPC p224n).pub (subFn p224n.k p224n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224n_sub_verified : Verified PPC64LE.target (subFn p224n.k p224n.m) (p224n.subContract PPC64LE.abi) :=
  sub_verified p224n p224n_ok p224n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
