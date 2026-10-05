import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): P-256

P-256 as the proof's curve (`p256`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-256's sizes, which is `Proof.Ecdsa.X86.signX86`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- P-256, with the group law `hL`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.X86.signP256
  coreX := Proof.Ecdsa.X86.sign_x86 hL
  coreCT := Proof.Ecdsa.X86.sign_ct
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.X86
