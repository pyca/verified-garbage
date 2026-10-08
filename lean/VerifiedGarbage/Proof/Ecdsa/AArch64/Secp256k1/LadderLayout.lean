import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep

/-! # The general secp256k1 ladder's scratch slots -/

namespace VG.Proof.Ecdsa.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.Secp256k1
open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem ladLay : LadLay ladderCfg size := by
  constructor
  · refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
    have h : ∀ x ∈ ladSlots ladderCfg, ∀ y ∈ ladSlots ladderCfg,
        x ≠ y → x + 32 ≤ y ∨ y + 32 ≤ x := by decide +kernel
    exact fun x y hx hy => h x hx y hy
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide
  · decide
  · decide +kernel

theorem ladA : LadA ladderCfg where
  sl := by decide +kernel
  mod := MP'_A secp256k1
  bits := by decide
  call := by intro f m h; cases h

theorem ladW_eq : ladW ladderCfg = slW secp256k1
    [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
      T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] := rfl

end VG.Proof.Ecdsa.AArch64.Secp256k1
