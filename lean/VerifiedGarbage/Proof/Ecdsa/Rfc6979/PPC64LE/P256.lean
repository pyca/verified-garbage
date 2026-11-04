module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.P256

/-!
# Deterministic ECDSA on PPC64LE: P-256

P-256 as the proof's curve (`p256C`): its signature with a given `k`
(`vg_ecdsa_p256_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`p256_sizes`), the
taint checks of the blocks that depend on them (`p256_cblk`), and
`vg_ecdsa_p256_sign`, with the tables of `vs`, verified against
`TableInstance.signContract` (`p256_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p256_sign_k`, the signature with a given `k`, with P-256's group law `hL`. -/
def p256Core (hL : Weierstrass.Law Spec.P256.curve) : Core where
  E := Spec.Ecdsa.P256.inst
  C := Impl.Ecdsa.PPC64LE.signP256
  N := "vg_ecdsa_p256_sign_k"
  V := (Proof.Ecdsa.PPC64LE.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.sign_verified hL).2.1
  d := by decide +kernel

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem p256_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.P256.inst 8 (cfgS Spec.Ecdsa.P256.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem p256_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.P256.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- P-256, with its group law `hL`. -/
def p256C (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve := ⟨p256Core hL, 8, p256_sizes, p256_cblk⟩

theorem p256T (hL : Weierstrass.Law Spec.P256.curve) : CurveT (p256C hL) Spec.Ecdsa.Rfc6979.Curves.p256 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p256_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p256_verified (hL : Weierstrass.Law Spec.P256.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p256C hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 vs) :=
  signT_verified (p256T hL) rfl hO (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
