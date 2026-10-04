import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P384Sha384

/-!
# Deterministic ECDSA over P-384 with HMAC-SHA-384 on x86-64

SHA-384, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract` for 240 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p384_sha384_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P384Sha384

open VG VG.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

theorem implies :
    (rfcX86_64 Spec.Ecdsa.Rfc6979.P384Sha384.inst).Implies
      (Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract X86_64.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P384Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P384.inst, Spec.P384.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, satState] [satState 48 48] using satState 48 48 }

/-- SHA-384, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.P384.curve) (v : Compress) : RfcHash where
  R := p384 hL
  I := Spec.Ecdsa.Rfc6979.P384Sha384.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha512.sha384H v
  ok := Proof.Pbkdf2.Md.X86_64.Sha512.sha384OK v
  C := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha512.sha384K v
  satI := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl
  updSp := show (Proof.Pbkdf2.Md.X86_64.Sha512.coreH 48).updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.P384.curve) (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL v)).sign
      (Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract X86_64.abi 240) :=
  X86_64.sign_verified (pack hL v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.P384Sha384
