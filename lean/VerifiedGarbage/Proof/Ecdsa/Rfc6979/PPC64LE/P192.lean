module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
meta import VerifiedGarbage.Spec.Ecdsa.P192

/-!
# Deterministic ECDSA on PPC64LE: P-192

P-192 as the proof's curve (`p192C`): its signature with a given `k`
(`vg_ecdsa_p192_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`p192_sizes`), the
taint checks of the blocks that depend on them (`p192_cblk`). `Verified.lean`
verifies `vg_ecdsa_p192_sign` with it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p192_sign_k`, the signature with a given `k`, with P-192's group law `hL`. -/
def p192Core (hL : Weierstrass.Law Spec.P192.curve) : Core where
  E := Spec.Ecdsa.P192.inst
  C := Impl.Ecdsa.PPC64LE.signP192
  N := "vg_ecdsa_p192_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P192.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P192.sign_verified hL).2.1
  d := by decide +kernel

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem p192_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.P192.inst 6 (cfgS Spec.Ecdsa.P192.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem p192_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.P192.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- P-192, with its group law `hL`. -/
def p192C (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve := ⟨p192Core hL, 6, p192_sizes, p192_cblk⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
