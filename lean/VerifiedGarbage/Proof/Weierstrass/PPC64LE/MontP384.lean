module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo P384's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem p384p_mul_ct : ConstantTime isa (mulPPC p384p).pre (mulPPC p384p).pub (mulFn p384p.k p384p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384p_mul_verified : Verified PPC64LE.target (mulFn p384p.k p384p.m) (p384p.mulContract PPC64LE.abi) :=
  mul_verified p384p p384p_ok p384p_mul_ct

theorem p384p_add_ct : ConstantTime isa (addPPC p384p).pre (addPPC p384p).pub (addFn p384p.k p384p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384p_add_verified : Verified PPC64LE.target (addFn p384p.k p384p.m) (p384p.addContract PPC64LE.abi) :=
  add_verified p384p p384p_ok p384p_add_ct

theorem p384p_sub_ct : ConstantTime isa (subPPC p384p).pre (subPPC p384p).pub (subFn p384p.k p384p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384p_sub_verified : Verified PPC64LE.target (subFn p384p.k p384p.m) (p384p.subContract PPC64LE.abi) :=
  sub_verified p384p p384p_ok p384p_sub_ct

theorem p384n_mul_ct : ConstantTime isa (mulPPC p384n).pre (mulPPC p384n).pub (mulFn p384n.k p384n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384n_mul_verified : Verified PPC64LE.target (mulFn p384n.k p384n.m) (p384n.mulContract PPC64LE.abi) :=
  mul_verified p384n p384n_ok p384n_mul_ct

theorem p384n_add_ct : ConstantTime isa (addPPC p384n).pre (addPPC p384n).pub (addFn p384n.k p384n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384n_add_verified : Verified PPC64LE.target (addFn p384n.k p384n.m) (p384n.addContract PPC64LE.abi) :=
  add_verified p384n p384n_ok p384n_add_ct

theorem p384n_sub_ct : ConstantTime isa (subPPC p384n).pre (subPPC p384n).pub (subFn p384n.k p384n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384n_sub_verified : Verified PPC64LE.target (subFn p384n.k p384n.m) (p384n.subContract PPC64LE.abi) :=
  sub_verified p384n p384n_ok p384n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
