module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo P521's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem p521p_mul_ct : ConstantTime isa (mulPPC p521p).pre (mulPPC p521p).pub (mulFn p521p.k p521p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521p_mul_verified : Verified PPC64LE.target (mulFn p521p.k p521p.m) (p521p.mulContract PPC64LE.abi) :=
  mul_verified p521p p521p_ok p521p_mul_ct

theorem p521p_add_ct : ConstantTime isa (addPPC p521p).pre (addPPC p521p).pub (addFn p521p.k p521p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521p_add_verified : Verified PPC64LE.target (addFn p521p.k p521p.m) (p521p.addContract PPC64LE.abi) :=
  add_verified p521p p521p_ok p521p_add_ct

theorem p521p_sub_ct : ConstantTime isa (subPPC p521p).pre (subPPC p521p).pub (subFn p521p.k p521p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521p_sub_verified : Verified PPC64LE.target (subFn p521p.k p521p.m) (p521p.subContract PPC64LE.abi) :=
  sub_verified p521p p521p_ok p521p_sub_ct

theorem p521n_mul_ct : ConstantTime isa (mulPPC p521n).pre (mulPPC p521n).pub (mulFn p521n.k p521n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521n_mul_verified : Verified PPC64LE.target (mulFn p521n.k p521n.m) (p521n.mulContract PPC64LE.abi) :=
  mul_verified p521n p521n_ok p521n_mul_ct

theorem p521n_add_ct : ConstantTime isa (addPPC p521n).pre (addPPC p521n).pub (addFn p521n.k p521n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521n_add_verified : Verified PPC64LE.target (addFn p521n.k p521n.m) (p521n.addContract PPC64LE.abi) :=
  add_verified p521n p521n_ok p521n_add_ct

theorem p521n_sub_ct : ConstantTime isa (subPPC p521n).pre (subPPC p521n).pub (subFn p521n.k p521n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521n_sub_verified : Verified PPC64LE.target (subFn p521n.k p521n.m) (p521n.subContract PPC64LE.abi) :=
  sub_verified p521n p521n_ok p521n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
