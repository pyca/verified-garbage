import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P256
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx

/-!
# Deterministic ECDSA on x86-64: P-256 with BMI2 and ADX

As `P256.lean`, with `vg_ecdsa_p256_sign_adx` (`p256x`, P-256 multiplying
with BMI2 and ADX), proven correct and constant time against the same
contract; `p256Of` is either.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` is the same for `p256x` as for `p256`, the same curve. -/
theorem coreK_p256x : coreK Impl.Ecdsa.X86_64.p256x = Proof.Ecdsa.X86_64.signX86_64 := coreK_p256

/-- P-256 with BMI2 and ADX, with the group law `hL`, the comb's tables `hT`
and the inversions' soundness `hI`. -/
def p256x (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p256x
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.p256_sh
  coreN := Spec.Ecdsa.P256.signApi.name ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP256Adx
  coreX := by rw [coreK_p256x]; exact fun s h _ => Proof.Ecdsa.X86_64.sign_x86_adx hL hT hI s h
  coreCT := by rw [coreK_p256x]; exact Proof.Ecdsa.X86_64.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceSp := Function.const _ (by decide +kernel)
  reduceMx := Function.const _ (by decide +kernel)

/-- P-256 with BMI2 and ADX (`adx`) or without. -/
def p256Of (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p256x hL hT hI else p256 hL hT hI

end VG.Proof.Ecdsa.Rfc6979.X86_64
