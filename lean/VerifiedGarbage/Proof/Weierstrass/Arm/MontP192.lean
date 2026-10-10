import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified

/-!
# Montgomery arithmetic modulo P-192's `p` and `n`, as functions, on 32-bit ARM: verified

P-192's moduli, in three 64-bit words, are ones the functions support
(`ModOk`), so each of their functions meets the contract of its `Api`, as
the other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Spec.Weierstrass.Mont

theorem p192p_ok : ModOk p192p.k p192p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p192n_ok : ModOk p192n.k p192n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p192p_mul_ct : ConstantTime isa (mulArm p192p).pre (mulArm p192p).pub (mulFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p192p_mul_verified : Verified Arm.target (mulFn p192p.k p192p.m) (p192p.mulContract Arm.abi) :=
  mul_verified p192p p192p_ok (by decide) p192p_mul_ct

theorem p192p_add_ct : ConstantTime isa (addArm p192p).pre (addArm p192p).pub (addFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p192p_add_verified : Verified Arm.target (addFn p192p.k p192p.m) (p192p.addContract Arm.abi) :=
  add_verified p192p p192p_ok (by decide) p192p_add_ct

theorem p192p_sub_ct : ConstantTime isa (subArm p192p).pre (subArm p192p).pub (subFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p192p_sub_verified : Verified Arm.target (subFn p192p.k p192p.m) (p192p.subContract Arm.abi) :=
  sub_verified p192p p192p_ok (by decide) p192p_sub_ct

theorem p192n_mul_ct : ConstantTime isa (mulArm p192n).pre (mulArm p192n).pub (mulFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p192n_mul_verified : Verified Arm.target (mulFn p192n.k p192n.m) (p192n.mulContract Arm.abi) :=
  mul_verified p192n p192n_ok (by decide) p192n_mul_ct

theorem p192n_add_ct : ConstantTime isa (addArm p192n).pre (addArm p192n).pub (addFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p192n_add_verified : Verified Arm.target (addFn p192n.k p192n.m) (p192n.addContract Arm.abi) :=
  add_verified p192n p192n_ok (by decide) p192n_add_ct

theorem p192n_sub_ct : ConstantTime isa (subArm p192n).pre (subArm p192n).pub (subFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p192n_sub_verified : Verified Arm.target (subFn p192n.k p192n.m) (p192n.subContract Arm.abi) :=
  sub_verified p192n p192n_ok (by decide) p192n_sub_ct

end VG.Proof.Weierstrass.Arm.Mont
