import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192

/-!
# Montgomery arithmetic modulo P-192's `p` and `n`, as functions, on x86 (32-bit): verified

P-192's moduli, in three 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Spec.Weierstrass.Mont

theorem p192p_ok : FnOk p192p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem p192n_ok : FnOk p192n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem p192p_mul_ct : ConstantTime isa (mulX86 p192p).pre (mulX86 p192p).pub (mulFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p192p_mul_verified : Verified X86.target (mulFn p192p.k p192p.m) (p192p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p192p_ok) p192p_mul_ct (mul_implies p192p p192p_ok.k9 p192p_ok.mul.m_pos)

theorem p192p_add_ct : ConstantTime isa (addX86 p192p).pre (addX86 p192p).pub (addFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p192p_add_verified : Verified X86.target (addFn p192p.k p192p.m) (p192p.addContract X86.abi) :=
  Verified.of_correct (add_x86 p192p_ok) p192p_add_ct (add_implies p192p p192p_ok.k9 p192p_ok.mul.m_pos)

theorem p192p_sub_ct : ConstantTime isa (subX86 p192p).pre (subX86 p192p).pub (subFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p192p_sub_verified : Verified X86.target (subFn p192p.k p192p.m) (p192p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p192p_ok) p192p_sub_ct (sub_implies p192p p192p_ok.k9 p192p_ok.mul.m_pos)

theorem p192n_mul_ct : ConstantTime isa (mulX86 p192n).pre (mulX86 p192n).pub (mulFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p192n_mul_verified : Verified X86.target (mulFn p192n.k p192n.m) (p192n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p192n_ok) p192n_mul_ct (mul_implies p192n p192n_ok.k9 p192n_ok.mul.m_pos)

theorem p192n_add_ct : ConstantTime isa (addX86 p192n).pre (addX86 p192n).pub (addFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p192n_add_verified : Verified X86.target (addFn p192n.k p192n.m) (p192n.addContract X86.abi) :=
  Verified.of_correct (add_x86 p192n_ok) p192n_add_ct (add_implies p192n p192n_ok.k9 p192n_ok.mul.m_pos)

theorem p192n_sub_ct : ConstantTime isa (subX86 p192n).pre (subX86 p192n).pub (subFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p192n_sub_verified : Verified X86.target (subFn p192n.k p192n.m) (p192n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p192n_ok) p192n_sub_ct (sub_implies p192n p192n_ok.k9 p192n_ok.mul.m_pos)

end VG.Proof.Weierstrass.X86.Mont
