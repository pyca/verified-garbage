module

import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontVerified
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.X86.Chain
meta import VerifiedGarbage.Proof.Mont.X86.Csub
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Spec.Rc2

/-!
# Montgomery arithmetic modulo P-192's `p` and `n`, as functions, on x86 (32-bit): verified

P-192's moduli, in three 64-bit words, are ones the functions support
(`FnOk`), so each of their functions meets the contract of its `Api`, as the
other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

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
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem p192p_mul_verified : Verified X86.target (mulFn p192p.k p192p.m) (p192p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p192p_ok) p192p_mul_ct (mul_implies p192p p192p_ok.k9 p192p_ok.mul.m_pos)

theorem p192p_add_ct : ConstantTime isa (addX86 p192p).pre (addX86 p192p).pub (addFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem p192p_add_verified : Verified X86.target (addFn p192p.k p192p.m) (p192p.addContract X86.abi) :=
  Verified.of_correct (add_x86 p192p_ok) p192p_add_ct (add_implies p192p p192p_ok.k9 p192p_ok.mul.m_pos)

theorem p192p_sub_ct : ConstantTime isa (subX86 p192p).pre (subX86 p192p).pub (subFn p192p.k p192p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem p192p_sub_verified : Verified X86.target (subFn p192p.k p192p.m) (p192p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p192p_ok) p192p_sub_ct (sub_implies p192p p192p_ok.k9 p192p_ok.mul.m_pos)

theorem p192n_mul_ct : ConstantTime isa (mulX86 p192n).pre (mulX86 p192n).pub (mulFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem p192n_mul_verified : Verified X86.target (mulFn p192n.k p192n.m) (p192n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p192n_ok) p192n_mul_ct (mul_implies p192n p192n_ok.k9 p192n_ok.mul.m_pos)

theorem p192n_add_ct : ConstantTime isa (addX86 p192n).pre (addX86 p192n).pub (addFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem p192n_add_verified : Verified X86.target (addFn p192n.k p192n.m) (p192n.addContract X86.abi) :=
  Verified.of_correct (add_x86 p192n_ok) p192n_add_ct (add_implies p192n p192n_ok.k9 p192n_ok.mul.m_pos)

theorem p192n_sub_ct : ConstantTime isa (subX86 p192n).pre (subX86 p192n).pub (subFn p192n.k p192n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by native_taint_decide)

theorem p192n_sub_verified : Verified X86.target (subFn p192n.k p192n.m) (p192n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p192n_ok) p192n_sub_ct (sub_implies p192n p192n_ok.k9 p192n_ok.mul.m_pos)

end VG.Proof.Weierstrass.X86.Mont
