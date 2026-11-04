module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1

/-!
# Deterministic ECDSA on PPC64LE: secp256k1

secp256k1 as the proof's curve (`secp256k1C`): its signature with a given `k`
(`vg_ecdsa_secp256k1_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`secp256k1_sizes`), the
taint checks of the blocks that depend on them (`secp256k1_cblk`), and
`vg_ecdsa_secp256k1_sign`, with the tables of `vs`, verified against
`TableInstance.signContract` (`secp256k1_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_secp256k1_sign_k`, the signature with a given `k`, with secp256k1's group law `hL`. -/
def secp256k1Core (hL : Weierstrass.Law Spec.Secp256k1.curve) : Core where
  E := Spec.Ecdsa.Secp256k1.inst
  C := Impl.Ecdsa.PPC64LE.signSecp256k1
  N := "vg_ecdsa_secp256k1_sign_k"
  V := (Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified hL).2.1
  d := by decide +kernel

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem secp256k1_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.Secp256k1.inst 8 (cfgS Spec.Ecdsa.Secp256k1.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem secp256k1_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.Secp256k1.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- secp256k1, with its group law `hL`. -/
def secp256k1C (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcCurve := ⟨secp256k1Core hL, 8, secp256k1_sizes, secp256k1_cblk⟩

theorem secp256k1T (hL : Weierstrass.Law Spec.Secp256k1.curve) : CurveT (secp256k1C hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem secp256k1_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (secp256k1C hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 vs) :=
  signT_verified (secp256k1T hL) rfl hO (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
