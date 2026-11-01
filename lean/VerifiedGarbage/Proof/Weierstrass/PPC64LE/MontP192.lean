module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo P192's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem p192p_mul_ct : ConstantTime isa (mulPPC p192p).pre (mulPPC p192p).pub (mulFn p192p.k p192p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p192p_mul_verified : Verified PPC64LE.target (mulFn p192p.k p192p.m) (p192p.mulContract PPC64LE.abi) :=
  mul_verified p192p p192p_ok p192p_mul_ct

theorem p192p_add_ct : ConstantTime isa (addPPC p192p).pre (addPPC p192p).pub (addFn p192p.k p192p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p192p_add_verified : Verified PPC64LE.target (addFn p192p.k p192p.m) (p192p.addContract PPC64LE.abi) :=
  add_verified p192p p192p_ok p192p_add_ct

theorem p192p_sub_ct : ConstantTime isa (subPPC p192p).pre (subPPC p192p).pub (subFn p192p.k p192p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p192p_sub_verified : Verified PPC64LE.target (subFn p192p.k p192p.m) (p192p.subContract PPC64LE.abi) :=
  sub_verified p192p p192p_ok p192p_sub_ct

theorem p192n_mul_ct : ConstantTime isa (mulPPC p192n).pre (mulPPC p192n).pub (mulFn p192n.k p192n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p192n_mul_verified : Verified PPC64LE.target (mulFn p192n.k p192n.m) (p192n.mulContract PPC64LE.abi) :=
  mul_verified p192n p192n_ok p192n_mul_ct

theorem p192n_add_ct : ConstantTime isa (addPPC p192n).pre (addPPC p192n).pub (addFn p192n.k p192n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p192n_add_verified : Verified PPC64LE.target (addFn p192n.k p192n.m) (p192n.addContract PPC64LE.abi) :=
  add_verified p192n p192n_ok p192n_add_ct

theorem p192n_sub_ct : ConstantTime isa (subPPC p192n).pre (subPPC p192n).pub (subFn p192n.k p192n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p192n_sub_verified : Verified PPC64LE.target (subFn p192n.k p192n.m) (p192n.subContract PPC64LE.abi) :=
  sub_verified p192n p192n_ok p192n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
