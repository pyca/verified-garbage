module

import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
import VerifiedGarbage.Impl.Weierstrass.Slots
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Impl.Weierstrass.Slots
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.X86_64.Blocks
meta import VerifiedGarbage.Proof.Mont.X86_64.CsubS
meta import VerifiedGarbage.Proof.Mont.X86_64.Friendly
meta import VerifiedGarbage.Proof.Mont.X86_64.Round
meta import VerifiedGarbage.Proof.Mont.X86_64.Sparse
meta import VerifiedGarbage.Proof.Mont.X86_64.SparseX
meta import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Mont.X86_64.WideOps
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# P-521's product modulo `n` as a function, on x86-64: verified

`p521n.mulContract` on x86-64, by register (`mulX64`), which `mulFnN` meets
(`mulFnN_x64`, from `mulFnN_ok` by `fn9_x64`), constant time by taint
tracking (only the stack pointer, `ws` and the offsets' low halves are
public), and a state satisfying it (`mul_implies`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus p521n)

theorem p521n_m : p521n.m = n521 := by decide +kernel

theorem p521n_R : p521n.R = (2 ^ 64) ^ 9 :=
  (Nat.pow_mul 2 64 p521n.k).trans (congrArg (HPow.hPow (2 ^ 64)) (show p521n.k = 9 from rfl))

theorem mulFnN_x64 : ∀ s, (mulX64 p521n).pre s →
    ∃ t s', Exec isa mulFnN s t s' ∧ abiPreserved s s' ∧ (mulX64 p521n).post s s' :=
  fn9_x64 p521n rfl p521n_R (by decide +kernel) fun hs hZ ho ha hb hB => by
    rw [p521n_m] at hB ⊢
    exact WP.mono (mulFnN_ok hs hZ ho ha hb hB) fun _ h => h

theorem mulFnN_ct : ConstantTime isa (mulX64 p521n).pre (mulX64 p521n).pub mulFnN :=
  ct_zext (M := p521n) (fun _ h => h.1)
    (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))

/-- `vg_p521_mul_mod_n` on x86-64. -/
theorem p521n_mul_verified : Verified X86_64.target mulFnN (p521n.mulContract X86_64.abi) :=
  Verified.of_correct mulFnN_x64 mulFnN_ct (mul_implies p521n (by decide) (by decide +kernel))

end VG.Proof.Weierstrass.X86_64.Mont
