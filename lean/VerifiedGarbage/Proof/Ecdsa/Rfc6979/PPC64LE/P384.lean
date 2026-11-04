module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.P384

/-!
# Deterministic ECDSA on PPC64LE: P-384

P-384 as the proof's curve (`p384C`): its signature with a given `k`
(`vg_ecdsa_p384_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`p384_sizes`), the
taint checks of the blocks that depend on them (`p384_cblk`), and
`vg_ecdsa_p384_sign`, with the tables of `vs`, verified against
`TableInstance.signContract` (`p384_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p384_sign_k`, the signature with a given `k`, with P-384's group law `hL`. -/
def p384Core (hL : Weierstrass.Law Spec.P384.curve) : Core where
  E := Spec.Ecdsa.P384.inst
  C := Impl.Ecdsa.PPC64LE.signP384
  N := "vg_ecdsa_p384_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P384.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P384.sign_verified hL).2.1
  d := by decide +kernel

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem p384_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.P384.inst 12 (cfgS Spec.Ecdsa.P384.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem p384_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.P384.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- P-384, with its group law `hL`. -/
def p384C (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve := ⟨p384Core hL, 12, p384_sizes, p384_cblk⟩

theorem p384T (hL : Weierstrass.Law Spec.P384.curve) : CurveT (p384C hL) Spec.Ecdsa.Rfc6979.Curves.p384 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p384_verified (hL : Weierstrass.Law Spec.P384.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p384C hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 vs) :=
  signT_verified (p384T hL) rfl hO (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
