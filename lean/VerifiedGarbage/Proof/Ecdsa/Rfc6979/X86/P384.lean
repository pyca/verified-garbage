import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): P-384

P-384 as the proof's curve (`p384`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-384's sizes, which is `Proof.Ecdsa.X86.P384.signX86`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- P-384, with the group law `hL`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr rfl, rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := Spec.Ecdsa.P384.signApi.name
  coreC := Impl.Ecdsa.X86.signP384
  coreX := Proof.Ecdsa.X86.P384.sign_x86 hL
  coreCT := Proof.Ecdsa.X86.P384.sign_ct
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.X86
