import VerifiedGarbage.Proof.Dsa.X86_64.Backend

/-! # BMI2/ADX Montgomery arithmetic for DSA: calls of `vg_rsa_mont_mul_adx` -/
namespace VG.Variants.DsaArithmetic.X86_64.Adx
open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend where
  mm := CallMont.adx.mm
  mont := CallMont.adx.mont
  note := "Montgomery multiplication by calls of `vg_rsa_mont_mul_adx`"
  suffix := "_adx"
  features := ["bmi2", "adx"]
  signIn := by decide +kernel
  verifyIn := by decide +kernel
  signEq := rfl
  verifyEq := rfl
  signMx := by decide +kernel
  verifyMx := by decide +kernel
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)

end VG.Variants.DsaArithmetic.X86_64.Adx
