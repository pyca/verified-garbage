import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P521
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512 on x86 (32-bit)

The hash function for the generic proof: SHA-512's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.X86.sha512OKF`), and `vg_ecdsa_p521_sign`,
with P-521's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86.P521Sha512

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.P521Sha512.inst 416).Implies
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract X86.abi 416) := by
  have a0 : arg (satState 66 64) 0 = 0x1000 := by decide
  have a1 : arg (satState 66 64) 1 = 0x2000 := by decide
  have a2 : arg (satState 66 64) 2 = 0x3000 := by decide
  have a3 : arg (satState 66 64) 3 = 0x8000 := by decide
  have e : argAddr (satState 66 64) 0 = 0x20004 := by decide
  have esp : (satState 66 64).gpr .esp = 0x20000 := rfl
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, by simp⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true] [a0, a1, a2, a3, e, esp]
          using satState 66 64 }

/-- SHA-512, for P-521's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P521.curve) : RfcHash where
  R := p521 hL
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  F := Proof.Pbkdf2.Whole.X86.sha512F
  ok := Proof.Pbkdf2.Whole.X86.sha512OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
    exact Proof.Hmac.Generic.Common.finalHash_length _ _
  tries := rfl
  hDB := .inr (.inr ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hQ := ⟨rfl, rfl⟩

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified X86.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract X86.abi 416) :=
  X86.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.X86.P521Sha512
