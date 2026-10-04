import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384 on AArch64

SHA-384, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract` for 240 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p256_sha384_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.Sha384

open VG VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)


theorem implies :
    (rfcAArch64 Spec.Ecdsa.Rfc6979.P256Sha384.inst).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract AArch64.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          AArch64.abi, AArch64.argRegs, rfcAArch64, below]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          AArch64.abi, AArch64.argRegs, rfcAArch64, below]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          AArch64.abi, AArch64.argRegs, rfcAArch64, below] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          AArch64.abi, AArch64.argRegs, satState, below] [satState 48] using satState 48 }

/-- SHA-384, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOk Spec.P256.curve 64 Impl.P256.p256Comb Impl.P256.p256CombStart) (v : Compress) :
    RfcHash where
  I := Spec.Ecdsa.Rfc6979.P256Sha384.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha512.hash v Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name Spec.Sha512.H0_384
  ok := Proof.Pbkdf2.Md.AArch64.Sha512.ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl
    (Or.inl rfl)
  C := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  coreX := Proof.Ecdsa.AArch64.sign_a64 hL hT
  coreCT := Proof.Ecdsa.AArch64.sign_ct

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOk Spec.P256.curve 64 Impl.P256.p256Comb Impl.P256.p256CombStart) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hT v)).sign
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract AArch64.abi 240) :=
  AArch64.sign_verified (pack hL hT v) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.Sha384
