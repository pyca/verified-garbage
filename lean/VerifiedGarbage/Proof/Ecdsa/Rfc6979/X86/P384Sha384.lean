import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P384
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P384Sha384

/-!
# Deterministic ECDSA over P-384 with HMAC-SHA-384 on x86 (32-bit)

The hash function for the generic proof: SHA-384's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.X86.sha384OKF`), and `vg_ecdsa_p384_sign`,
with P-384's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86.P384Sha384

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.P384Sha384.inst).Implies
      (Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract X86.abi 272) := by
  have a0 : arg (satState 48 48) 0 = 0x1000 := by decide
  have a1 : arg (satState 48 48) 1 = 0x2000 := by decide
  have a2 : arg (satState 48 48) 2 = 0x3000 := by decide
  have a3 : arg (satState 48 48) 3 = 0x8000 := by decide
  have e : argAddr (satState 48 48) 0 = 0x20004 := by decide
  have esp : (satState 48 48).gpr .esp = 0x20000 := rfl
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86] [a0, a1, a2, a3, e, esp]
          using satState 48 48 }

/-- SHA-384, for P-384's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P384.curve) : RfcHash where
  R := p384 hL
  I := Spec.Ecdsa.Rfc6979.P384Sha384.inst
  F := Proof.Pbkdf2.Whole.X86.sha384F
  ok := Proof.Pbkdf2.Whole.X86.sha384OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
    rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl
  tries := rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified X86.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract X86.abi 272) :=
  X86.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.X86.P384Sha384
