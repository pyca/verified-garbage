module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.X25519.X86.Column
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Spec.Rc2

/-!
# Montgomery arithmetic modulo secp256k1's `p` and `n`, as functions, on x86 (32-bit): verified

secp256k1's moduli, in four 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Spec.Weierstrass.Mont

theorem secp256k1p_ok : FnOk secp256k1p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem secp256k1n_ok : FnOk secp256k1n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem secp256k1p_mul_ct : ConstantTime isa (mulX86 secp256k1p).pre (mulX86 secp256k1p).pub (mulFn secp256k1p.k secp256k1p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem secp256k1p_mul_verified : Verified X86.target (mulFn secp256k1p.k secp256k1p.m) (secp256k1p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 secp256k1p_ok) secp256k1p_mul_ct (mul_implies secp256k1p secp256k1p_ok.k9 secp256k1p_ok.mul.m_pos)

theorem secp256k1p_add_ct : ConstantTime isa (addX86 secp256k1p).pre (addX86 secp256k1p).pub (addFn secp256k1p.k secp256k1p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem secp256k1p_add_verified : Verified X86.target (addFn secp256k1p.k secp256k1p.m) (secp256k1p.addContract X86.abi) :=
  Verified.of_correct (add_x86 secp256k1p_ok) secp256k1p_add_ct (add_implies secp256k1p secp256k1p_ok.k9 secp256k1p_ok.mul.m_pos)

theorem secp256k1p_sub_ct : ConstantTime isa (subX86 secp256k1p).pre (subX86 secp256k1p).pub (subFn secp256k1p.k secp256k1p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem secp256k1p_sub_verified : Verified X86.target (subFn secp256k1p.k secp256k1p.m) (secp256k1p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 secp256k1p_ok) secp256k1p_sub_ct (sub_implies secp256k1p secp256k1p_ok.k9 secp256k1p_ok.mul.m_pos)

theorem secp256k1n_mul_ct : ConstantTime isa (mulX86 secp256k1n).pre (mulX86 secp256k1n).pub (mulFn secp256k1n.k secp256k1n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem secp256k1n_mul_verified : Verified X86.target (mulFn secp256k1n.k secp256k1n.m) (secp256k1n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 secp256k1n_ok) secp256k1n_mul_ct (mul_implies secp256k1n secp256k1n_ok.k9 secp256k1n_ok.mul.m_pos)

theorem secp256k1n_add_ct : ConstantTime isa (addX86 secp256k1n).pre (addX86 secp256k1n).pub (addFn secp256k1n.k secp256k1n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem secp256k1n_add_verified : Verified X86.target (addFn secp256k1n.k secp256k1n.m) (secp256k1n.addContract X86.abi) :=
  Verified.of_correct (add_x86 secp256k1n_ok) secp256k1n_add_ct (add_implies secp256k1n secp256k1n_ok.k9 secp256k1n_ok.mul.m_pos)

theorem secp256k1n_sub_ct : ConstantTime isa (subX86 secp256k1n).pre (subX86 secp256k1n).pub (subFn secp256k1n.k secp256k1n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem secp256k1n_sub_verified : Verified X86.target (subFn secp256k1n.k secp256k1n.m) (secp256k1n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 secp256k1n_ok) secp256k1n_sub_ct (sub_implies secp256k1n secp256k1n_ok.k9 secp256k1n_ok.mul.m_pos)

end VG.Proof.Weierstrass.X86.Mont
