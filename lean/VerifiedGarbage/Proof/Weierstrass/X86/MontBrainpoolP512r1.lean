module

import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
public import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# Montgomery arithmetic modulo brainpoolP512r1's `p` and `n`, as functions, on x86 (32-bit): verified

brainpoolP512r1's moduli, in eight 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Impl.Weierstrass.Mont

theorem brainpoolp512r1p_ok : FnOk brainpoolp512r1p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem brainpoolp512r1n_ok : FnOk brainpoolp512r1n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by lit_decide)
  nsAdd := NoSp.of_all (by lit_decide)
  nsSub := NoSp.of_all (by lit_decide)

theorem brainpoolp512r1p_mul_ct : ConstantTime isa (mulX86 brainpoolp512r1p).pre (mulX86 brainpoolp512r1p).pub (mulFn brainpoolp512r1p.k brainpoolp512r1p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem brainpoolp512r1p_mul_verified : Verified X86.target (mulFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 brainpoolp512r1p_ok) brainpoolp512r1p_mul_ct (mul_implies brainpoolp512r1p brainpoolp512r1p_ok.k9 brainpoolp512r1p_ok.mul.m_pos)

theorem brainpoolp512r1p_add_ct : ConstantTime isa (addX86 brainpoolp512r1p).pre (addX86 brainpoolp512r1p).pub (addFn brainpoolp512r1p.k brainpoolp512r1p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem brainpoolp512r1p_add_verified : Verified X86.target (addFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.addContract X86.abi) :=
  Verified.of_correct (add_x86 brainpoolp512r1p_ok) brainpoolp512r1p_add_ct (add_implies brainpoolp512r1p brainpoolp512r1p_ok.k9 brainpoolp512r1p_ok.mul.m_pos)

theorem brainpoolp512r1p_sub_ct : ConstantTime isa (subX86 brainpoolp512r1p).pre (subX86 brainpoolp512r1p).pub (subFn brainpoolp512r1p.k brainpoolp512r1p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem brainpoolp512r1p_sub_verified : Verified X86.target (subFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 brainpoolp512r1p_ok) brainpoolp512r1p_sub_ct (sub_implies brainpoolp512r1p brainpoolp512r1p_ok.k9 brainpoolp512r1p_ok.mul.m_pos)

theorem brainpoolp512r1n_mul_ct : ConstantTime isa (mulX86 brainpoolp512r1n).pre (mulX86 brainpoolp512r1n).pub (mulFn brainpoolp512r1n.k brainpoolp512r1n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem brainpoolp512r1n_mul_verified : Verified X86.target (mulFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 brainpoolp512r1n_ok) brainpoolp512r1n_mul_ct (mul_implies brainpoolp512r1n brainpoolp512r1n_ok.k9 brainpoolp512r1n_ok.mul.m_pos)

theorem brainpoolp512r1n_add_ct : ConstantTime isa (addX86 brainpoolp512r1n).pre (addX86 brainpoolp512r1n).pub (addFn brainpoolp512r1n.k brainpoolp512r1n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem brainpoolp512r1n_add_verified : Verified X86.target (addFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.addContract X86.abi) :=
  Verified.of_correct (add_x86 brainpoolp512r1n_ok) brainpoolp512r1n_add_ct (add_implies brainpoolp512r1n brainpoolp512r1n_ok.k9 brainpoolp512r1n_ok.mul.m_pos)

theorem brainpoolp512r1n_sub_ct : ConstantTime isa (subX86 brainpoolp512r1n).pre (subX86 brainpoolp512r1n).pub (subFn brainpoolp512r1n.k brainpoolp512r1n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem brainpoolp512r1n_sub_verified : Verified X86.target (subFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 brainpoolp512r1n_ok) brainpoolp512r1n_sub_ct (sub_implies brainpoolp512r1n brainpoolp512r1n_ok.k9 brainpoolp512r1n_ok.mul.m_pos)

end VG.Proof.Weierstrass.X86.Mont
