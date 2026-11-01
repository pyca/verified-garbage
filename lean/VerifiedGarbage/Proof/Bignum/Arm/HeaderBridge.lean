module

public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The existing 64-bit RSA workspace as native ARMv7 words -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout)

theorem read32_low (mem : Mem) (base : Addr) (d : Nat) :
    w32 mem base d = (word mem base d).toNat % 2 ^ 32 := by
  rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem.readW (off base d) 32).isLt]

theorem numAt_native (mem : Mem) (base : Addr) (w j : Nat) :
    numAt mem base w j = val32 mem base (arrAt w j) (2 * w) := by
  unfold numAt
  rw [read_eq_wordsVal, wordsVal_eq_val32]

theorem array_end_le {w j k : Nat} (h : j < k) : arrAt w j + 8 * (w + 2) ≤ arrAt w k := by
  have := Nat.mul_le_mul_right (8 * (w + 2)) h
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, Nat.succ_mul] at *
  omega

theorem nativeHeader_of_layout (mem : Mem) (base : BitVec 32) {size len : Nat}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fits : 8 * len ≤ size)
    (layout : Layout mem (State.addr base) len) :
    NativeHeader mem base (wOf mem (State.addr base)) (arrAt (wOf mem (State.addr base)))
      (BitVec.ofNat 32 (wordAt mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat) := by
  let w := wOf mem (State.addr base)
  obtain ⟨hw, _, arraysFit, arrays⟩ := layout
  change arrAt w 8 ≤ 8 * len at arraysFit
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact read32_low mem (State.addr base) 48
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact read32_low mem (State.addr base) 56
  · intro j hj
    have aj := array_end_le (w := w) hj
    have bound : base.toNat + arrAt w j < 2 ^ 32 := by omega
    have address := arrays j hj
    change word mem (State.addr base) (8 * (8 + j)) = off (State.addr base) (arrAt w j) at address
    have addrEq : 8 * (8 + j) = 64 + 8 * j := by omega
    rw [addrEq] at address
    apply BitVec.eq_of_toNat_eq
    change w32 mem (State.addr base) (64 + 8 * j) = (base + BitVec.ofNat 32 (arrAt w j)).toNat
    rw [read32_low, address]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X25519.Arm.addr_toNat]
    rw [Nat.mod_eq_of_lt (by omega : arrAt w j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : base.toNat + arrAt w j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : arrAt w j < 2 ^ 32)]


theorem native_inverse (mem : Mem) (base : Addr) {w : Nat} (hw : 0 < w)
    (h : ((word mem base (arrAt w 0)).toNat *
      (wordAt mem base Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0) :
    (val32 mem base (arrAt w 0) (2 * w) *
      (BitVec.ofNat 32 (wordAt mem base Proof.Rsa.Mont.minvWord).toNat).toNat + 1) % 2 ^ 32 = 0 := by
  have inv := inverse32 h
  have low : val32 mem base (arrAt w 0) (2 * w) % 2 ^ 32 =
      (word mem base (arrAt w 0)).toNat % 2 ^ 32 := by
    rw [show 2 * w = (2 * w - 1) + 1 by omega, val32_mod_low, read32_low]
  rw [BitVec.toNat_ofNat, Nat.add_mod, Nat.mul_mod, low, ← Nat.mul_mod, ← Nat.add_mod]
  exact inv

end VG.Proof.Bignum.Arm
