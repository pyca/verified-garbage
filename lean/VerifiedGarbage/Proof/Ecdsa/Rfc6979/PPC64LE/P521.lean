module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
meta import VerifiedGarbage.Spec.Ecdsa.P521

/-!
# Deterministic ECDSA on PPC64LE: P-521

P-521 as the proof's curve (`p521C`): its signature with a given `k`
(`vg_ecdsa_p521_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`p521_sizes`), the
taint checks of the blocks that depend on them (`p521_cblk`). `Verified.lean`
verifies `vg_ecdsa_p521_sign` with it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p521_sign_k`, the signature with a given `k`, with P-521's group law `hL`. -/
def p521Core (hL : Weierstrass.Law Spec.P521.curve) : Core where
  E := Spec.Ecdsa.P521.inst
  C := Impl.Ecdsa.PPC64LE.signP521
  N := "vg_ecdsa_p521_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P521.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P521.sign_verified hL).2.1
  d := by decide +kernel

theorem p521_nBits : Spec.Ecdsa.nBits Spec.P521.curve = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h₁ : 520 ≤ Spec.P521.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P521.curve.n.log2 < 521 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem p521_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.P521.inst 0 (cfgS Spec.Ecdsa.P521.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem p521_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.P521.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- P-521, with its group law `hL`. -/
def p521C (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve := ⟨p521Core hL, 0, p521_sizes, p521_cblk⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
