module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo BrainpoolP256r1's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem brainpoolp256r1p_mul_ct : ConstantTime isa (mulPPC brainpoolp256r1p).pre (mulPPC brainpoolp256r1p).pub (mulFn brainpoolp256r1p.k brainpoolp256r1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp256r1p_mul_verified : Verified PPC64LE.target (mulFn brainpoolp256r1p.k brainpoolp256r1p.m) (brainpoolp256r1p.mulContract PPC64LE.abi) :=
  mul_verified brainpoolp256r1p brainpoolp256r1p_ok brainpoolp256r1p_mul_ct

theorem brainpoolp256r1p_add_ct : ConstantTime isa (addPPC brainpoolp256r1p).pre (addPPC brainpoolp256r1p).pub (addFn brainpoolp256r1p.k brainpoolp256r1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp256r1p_add_verified : Verified PPC64LE.target (addFn brainpoolp256r1p.k brainpoolp256r1p.m) (brainpoolp256r1p.addContract PPC64LE.abi) :=
  add_verified brainpoolp256r1p brainpoolp256r1p_ok brainpoolp256r1p_add_ct

theorem brainpoolp256r1p_sub_ct : ConstantTime isa (subPPC brainpoolp256r1p).pre (subPPC brainpoolp256r1p).pub (subFn brainpoolp256r1p.k brainpoolp256r1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp256r1p_sub_verified : Verified PPC64LE.target (subFn brainpoolp256r1p.k brainpoolp256r1p.m) (brainpoolp256r1p.subContract PPC64LE.abi) :=
  sub_verified brainpoolp256r1p brainpoolp256r1p_ok brainpoolp256r1p_sub_ct

theorem brainpoolp256r1n_mul_ct : ConstantTime isa (mulPPC brainpoolp256r1n).pre (mulPPC brainpoolp256r1n).pub (mulFn brainpoolp256r1n.k brainpoolp256r1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp256r1n_mul_verified : Verified PPC64LE.target (mulFn brainpoolp256r1n.k brainpoolp256r1n.m) (brainpoolp256r1n.mulContract PPC64LE.abi) :=
  mul_verified brainpoolp256r1n brainpoolp256r1n_ok brainpoolp256r1n_mul_ct

theorem brainpoolp256r1n_add_ct : ConstantTime isa (addPPC brainpoolp256r1n).pre (addPPC brainpoolp256r1n).pub (addFn brainpoolp256r1n.k brainpoolp256r1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp256r1n_add_verified : Verified PPC64LE.target (addFn brainpoolp256r1n.k brainpoolp256r1n.m) (brainpoolp256r1n.addContract PPC64LE.abi) :=
  add_verified brainpoolp256r1n brainpoolp256r1n_ok brainpoolp256r1n_add_ct

theorem brainpoolp256r1n_sub_ct : ConstantTime isa (subPPC brainpoolp256r1n).pre (subPPC brainpoolp256r1n).pub (subFn brainpoolp256r1n.k brainpoolp256r1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp256r1n_sub_verified : Verified PPC64LE.target (subFn brainpoolp256r1n.k brainpoolp256r1n.m) (brainpoolp256r1n.subContract PPC64LE.abi) :=
  sub_verified brainpoolp256r1n brainpoolp256r1n_ok brainpoolp256r1n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
