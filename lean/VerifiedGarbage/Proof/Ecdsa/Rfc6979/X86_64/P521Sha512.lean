import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P521
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512 on x86-64

SHA-512, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract` for 384 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p521_sha512_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P521Sha512

open VG VG.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

theorem implies :
    (rfcX86_64 Impl.Ecdsa.X86_64.p521.combConsts Spec.Ecdsa.Rfc6979.P521Sha512.inst 384).Implies
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract X86_64.abi 384) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64, TblsOk, p521_combConsts, Abi.constRegions, Abi.constsHeld,
          List.map_nil, List.append_nil, List.not_mem_nil, false_implies, implies_true, and_true]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, fun c hc => by simp [p521_combConsts] at hc⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, satState] [satState 66 64] using satState 66 64 }

/-- SHA-512, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.P521.curve) (v : Compress) : RfcHash where
  R := p521 hL
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha512.sha512H v
  ok := Proof.Pbkdf2.Md.X86_64.Sha512.sha512OK v
  C := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha512.sha512K v
  satI := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inr ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := ⟨rfl, rfl⟩
  updSp := show (Proof.Pbkdf2.Md.X86_64.Sha512.coreH 64).updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve) (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL v)).sign
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract X86_64.abi 384) :=
  X86_64.sign_verified (pack hL v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.P521Sha512
