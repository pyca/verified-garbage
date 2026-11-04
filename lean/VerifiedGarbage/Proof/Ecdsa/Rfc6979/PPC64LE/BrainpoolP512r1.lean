module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1

/-!
# Deterministic ECDSA on PPC64LE: brainpoolP512r1

brainpoolP512r1 as the proof's curve (`brainpoolp512r1C`): its signature with a given `k`
(`vg_ecdsa_brainpoolp512r1_sign_k`, proven correct given the group law and constant
time), the facts of its sizes with each hash function's (`brainpoolp512r1_sizes`), the
taint checks of the blocks that depend on them (`brainpoolp512r1_cblk`), and
`vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`, verified against
`TableInstance.signContract` (`brainpoolp512r1_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_brainpoolp512r1_sign_k`, the signature with a given `k`, with brainpoolP512r1's group law `hL`. -/
def brainpoolp512r1Core (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : Core where
  E := Spec.Ecdsa.BrainpoolP512r1.inst
  C := Impl.Ecdsa.PPC64LE.signBrainpoolP512r1
  N := "vg_ecdsa_brainpoolp512r1_sign_k"
  V := (Proof.Ecdsa.PPC64LE.BrainpoolP512r1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.BrainpoolP512r1.sign_verified hL).2.1
  d := by decide +kernel

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem brainpoolp512r1_sizes : ∀ i ∈ hidx, SizeOk Spec.Ecdsa.BrainpoolP512r1.inst 16 (cfgS Spec.Ecdsa.BrainpoolP512r1.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> size_ok

theorem brainpoolp512r1_cblk : ∀ i ∈ hidx, CBlks (cfgS Spec.Ecdsa.BrainpoolP512r1.inst i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cblk_ok

/-- brainpoolP512r1, with its group law `hL`. -/
def brainpoolp512r1C (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve := ⟨brainpoolp512r1Core hL, 16, brainpoolp512r1_sizes, brainpoolp512r1_cblk⟩

theorem brainpoolp512r1T (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : CurveT (brainpoolp512r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp512r1_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (brainpoolp512r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 vs) :=
  signT_verified (brainpoolp512r1T hL) rfl hO (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
