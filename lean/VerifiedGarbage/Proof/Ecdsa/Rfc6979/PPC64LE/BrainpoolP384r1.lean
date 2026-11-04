module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1

/-!
# Deterministic ECDSA on PPC64LE: brainpoolP384r1

brainpoolP384r1 as the proof's curve (`brainpoolp384r1C`): its signature with a given `k`
(`vg_ecdsa_brainpoolp384r1_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`brainpoolp384r1_sizes`), the
taint checks of the blocks that depend on them (`brainpoolp384r1_cblk`), and
`vg_ecdsa_brainpoolp384r1_sign`, with the tables of `vs`, verified against
`TableInstance.signContract` (`brainpoolp384r1_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_brainpoolp384r1_sign_k`, the signature with a given `k`, with brainpoolP384r1's group law `hL`. -/
def brainpoolp384r1Core (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : Core where
  E := Spec.Ecdsa.BrainpoolP384r1.inst
  C := Impl.Ecdsa.PPC64LE.signBrainpoolP384r1
  N := "vg_ecdsa_brainpoolp384r1_sign_k"
  V := (Proof.Ecdsa.PPC64LE.BrainpoolP384r1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.BrainpoolP384r1.sign_verified hL).2.1
  d := by decide +kernel

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP384r1.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem brainpoolp384r1_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.BrainpoolP384r1.inst 12 (cfgS Spec.Ecdsa.BrainpoolP384r1.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem brainpoolp384r1_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.BrainpoolP384r1.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- brainpoolP384r1, with its group law `hL`. -/
def brainpoolp384r1C (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : RfcCurve := ⟨brainpoolp384r1Core hL, 12, brainpoolp384r1_sizes, brainpoolp384r1_cblk⟩

theorem brainpoolp384r1T (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : CurveT (brainpoolp384r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_brainpoolp384r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp384r1_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (brainpoolp384r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 vs) :=
  signT_verified (brainpoolp384r1T hL) rfl hO (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
