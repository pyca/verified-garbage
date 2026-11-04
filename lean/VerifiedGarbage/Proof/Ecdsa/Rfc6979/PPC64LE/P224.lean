module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
meta import VerifiedGarbage.Spec.Ecdsa.P224

/-!
# Deterministic ECDSA on PPC64LE: P-224

P-224 as the proof's curve (`p224C`): its signature with a given `k`
(`vg_ecdsa_p224_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`p224_sizes`), the
taint checks of the blocks that depend on them (`p224_cblk`). `Verified.lean`
verifies `vg_ecdsa_p224_sign` with it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p224_sign_k`, the signature with a given `k`, with P-224's group law `hL`. -/
def p224Core (hL : Weierstrass.Law Spec.P224.curve) : Core where
  E := Spec.Ecdsa.P224.inst
  C := Impl.Ecdsa.PPC64LE.signP224
  N := "vg_ecdsa_p224_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P224.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P224.sign_verified hL).2.1
  d := by decide +kernel

theorem p224_nBits : Spec.Ecdsa.nBits Spec.P224.curve = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem p224_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.P224.inst 7 (cfgS Spec.Ecdsa.P224.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem p224_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.P224.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- P-224, with its group law `hL`. -/
def p224C (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve := ⟨p224Core hL, 7, p224_sizes, p224_cblk⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
