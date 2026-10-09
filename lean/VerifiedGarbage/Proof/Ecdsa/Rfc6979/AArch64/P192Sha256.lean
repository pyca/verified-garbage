import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P192
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P192Sha256

/-!
# Deterministic ECDSA over p192 with HMAC-SHA-256 on AArch64

SHA-256, with any implementation `v` of SHA-256's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract` for 256 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p192_sha256_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.P192Sha256

open VG VG.AArch64
open VG.Proof.Sha256.AArch64 (Compress)

def sat : State := { satState 24 32 (fun _ => 0) 0 with
  rd := [⟨0x2000, 24⟩, ⟨0x3000, 32⟩] }

theorem implies :
    (rfcAArch64 Impl.Ecdsa.AArch64.p192 Spec.Ecdsa.Rfc6979.P192Sha256.inst 256).Implies
      (Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract AArch64.abi 256) := by
  sig_implies [Spec.Ecdsa.Rfc6979.P192Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P192.inst, Spec.P192.curve,
    Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, rfcAArch64, TblOk, tableRegions, tableAddr,
    Impl.Ecdsa.AArch64.p192, Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, List.flatMap_nil, List.map_nil, List.flatten_nil, List.length_nil, empty_disjoint,
    List.not_mem_nil, false_implies, implies_true, forall_const, and_true, result,
    Spec.Ecdsa.Rfc6979.Instance.result, List.cons.injEq, below]
    [sat, satState] using sat

/-- SHA-256, with the implementation `v` of SHA-256's compression function. -/
def pack (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) (v : Compress) :
    RfcHash where
  R := p192 hL hI
  I := Spec.Ecdsa.Rfc6979.P192Sha256.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha256.hash v
  ok := Proof.Pbkdf2.Md.AArch64.Sha256.ok v
  C := Proof.Pbkdf2.Md.AArch64.Sha256.coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha256.satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha256.satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hI v)).sign
      (Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract AArch64.abi 256) :=
  Verified.of_correct (sign_a64 (pack hL hI v)) sign_ct implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.P192Sha256
