module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo P256's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem p256p_mul_ct : ConstantTime isa (mulPPC p256p).pre (mulPPC p256p).pub (mulFn p256p.k p256p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p256p_mul_verified : Verified PPC64LE.target (mulFn p256p.k p256p.m) (p256p.mulContract PPC64LE.abi) :=
  mul_verified p256p p256p_ok p256p_mul_ct

theorem p256p_add_ct : ConstantTime isa (addPPC p256p).pre (addPPC p256p).pub (addFn p256p.k p256p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p256p_add_verified : Verified PPC64LE.target (addFn p256p.k p256p.m) (p256p.addContract PPC64LE.abi) :=
  add_verified p256p p256p_ok p256p_add_ct

theorem p256p_sub_ct : ConstantTime isa (subPPC p256p).pre (subPPC p256p).pub (subFn p256p.k p256p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p256p_sub_verified : Verified PPC64LE.target (subFn p256p.k p256p.m) (p256p.subContract PPC64LE.abi) :=
  sub_verified p256p p256p_ok p256p_sub_ct

theorem p256n_mul_ct : ConstantTime isa (mulPPC p256n).pre (mulPPC p256n).pub (mulFn p256n.k p256n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p256n_mul_verified : Verified PPC64LE.target (mulFn p256n.k p256n.m) (p256n.mulContract PPC64LE.abi) :=
  mul_verified p256n p256n_ok p256n_mul_ct

theorem p256n_add_ct : ConstantTime isa (addPPC p256n).pre (addPPC p256n).pub (addFn p256n.k p256n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p256n_add_verified : Verified PPC64LE.target (addFn p256n.k p256n.m) (p256n.addContract PPC64LE.abi) :=
  add_verified p256n p256n_ok p256n_add_ct

theorem p256n_sub_ct : ConstantTime isa (subPPC p256n).pre (subPPC p256n).pub (subFn p256n.k p256n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p256n_sub_verified : Verified PPC64LE.target (subFn p256n.k p256n.m) (p256n.subContract PPC64LE.abi) :=
  sub_verified p256n p256n_ok p256n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
