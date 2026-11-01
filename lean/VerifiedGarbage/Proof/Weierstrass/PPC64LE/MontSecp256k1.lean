module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract

/-! # Montgomery arithmetic modulo Secp256k1's `p` and `n`, as functions, on PPC64LE: verified -/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

theorem secp256k1p_mul_ct : ConstantTime isa (mulPPC secp256k1p).pre (mulPPC secp256k1p).pub (mulFn secp256k1p.k secp256k1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem secp256k1p_mul_verified : Verified PPC64LE.target (mulFn secp256k1p.k secp256k1p.m) (secp256k1p.mulContract PPC64LE.abi) :=
  mul_verified secp256k1p secp256k1p_ok secp256k1p_mul_ct

theorem secp256k1p_add_ct : ConstantTime isa (addPPC secp256k1p).pre (addPPC secp256k1p).pub (addFn secp256k1p.k secp256k1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem secp256k1p_add_verified : Verified PPC64LE.target (addFn secp256k1p.k secp256k1p.m) (secp256k1p.addContract PPC64LE.abi) :=
  add_verified secp256k1p secp256k1p_ok secp256k1p_add_ct

theorem secp256k1p_sub_ct : ConstantTime isa (subPPC secp256k1p).pre (subPPC secp256k1p).pub (subFn secp256k1p.k secp256k1p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem secp256k1p_sub_verified : Verified PPC64LE.target (subFn secp256k1p.k secp256k1p.m) (secp256k1p.subContract PPC64LE.abi) :=
  sub_verified secp256k1p secp256k1p_ok secp256k1p_sub_ct

theorem secp256k1n_mul_ct : ConstantTime isa (mulPPC secp256k1n).pre (mulPPC secp256k1n).pub (mulFn secp256k1n.k secp256k1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem secp256k1n_mul_verified : Verified PPC64LE.target (mulFn secp256k1n.k secp256k1n.m) (secp256k1n.mulContract PPC64LE.abi) :=
  mul_verified secp256k1n secp256k1n_ok secp256k1n_mul_ct

theorem secp256k1n_add_ct : ConstantTime isa (addPPC secp256k1n).pre (addPPC secp256k1n).pub (addFn secp256k1n.k secp256k1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem secp256k1n_add_verified : Verified PPC64LE.target (addFn secp256k1n.k secp256k1n.m) (secp256k1n.addContract PPC64LE.abi) :=
  add_verified secp256k1n secp256k1n_ok secp256k1n_add_ct

theorem secp256k1n_sub_ct : ConstantTime isa (subPPC secp256k1n).pre (subPPC secp256k1n).pub (subFn secp256k1n.k secp256k1n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem secp256k1n_sub_verified : Verified PPC64LE.target (subFn secp256k1n.k secp256k1n.m) (secp256k1n.subContract PPC64LE.abi) :=
  sub_verified secp256k1n secp256k1n_ok secp256k1n_sub_ct

end VG.Proof.Weierstrass.PPC64LE.Mont
