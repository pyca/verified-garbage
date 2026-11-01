module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo BrainpoolP512r1's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem brainpoolp512r1p_mul_ct : ConstantTime isa (mulPPC brainpoolp512r1p).pre (mulPPC brainpoolp512r1p).pub (mulFn brainpoolp512r1p.k brainpoolp512r1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1p_mul_verified : Verified PPC64LE.target (mulFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.mulContract PPC64LE.abi) :=
  mul_verified brainpoolp512r1p brainpoolp512r1p_ok brainpoolp512r1p_mul_ct

theorem brainpoolp512r1p_add_ct : ConstantTime isa (addPPC brainpoolp512r1p).pre (addPPC brainpoolp512r1p).pub (addFn brainpoolp512r1p.k brainpoolp512r1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1p_add_verified : Verified PPC64LE.target (addFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.addContract PPC64LE.abi) :=
  add_verified brainpoolp512r1p brainpoolp512r1p_ok brainpoolp512r1p_add_ct

theorem brainpoolp512r1p_sub_ct : ConstantTime isa (subPPC brainpoolp512r1p).pre (subPPC brainpoolp512r1p).pub (subFn brainpoolp512r1p.k brainpoolp512r1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1p_sub_verified : Verified PPC64LE.target (subFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.subContract PPC64LE.abi) :=
  sub_verified brainpoolp512r1p brainpoolp512r1p_ok brainpoolp512r1p_sub_ct

theorem brainpoolp512r1n_mul_ct : ConstantTime isa (mulPPC brainpoolp512r1n).pre (mulPPC brainpoolp512r1n).pub (mulFn brainpoolp512r1n.k brainpoolp512r1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1n_mul_verified : Verified PPC64LE.target (mulFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.mulContract PPC64LE.abi) :=
  mul_verified brainpoolp512r1n brainpoolp512r1n_ok brainpoolp512r1n_mul_ct

theorem brainpoolp512r1n_add_ct : ConstantTime isa (addPPC brainpoolp512r1n).pre (addPPC brainpoolp512r1n).pub (addFn brainpoolp512r1n.k brainpoolp512r1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1n_add_verified : Verified PPC64LE.target (addFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.addContract PPC64LE.abi) :=
  add_verified brainpoolp512r1n brainpoolp512r1n_ok brainpoolp512r1n_add_ct

theorem brainpoolp512r1n_sub_ct : ConstantTime isa (subPPC brainpoolp512r1n).pre (subPPC brainpoolp512r1n).pub (subFn brainpoolp512r1n.k brainpoolp512r1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1n_sub_verified : Verified PPC64LE.target (subFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.subContract PPC64LE.abi) :=
  sub_verified brainpoolp512r1n brainpoolp512r1n_ok brainpoolp512r1n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
