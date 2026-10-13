module

public import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Equality masks for supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem widthMask_ok {s : State} {n value : Nat}
    (hn : n < 2 ^ 16) (hv : value < 2 ^ 64) (h8 : s.gpr .x8 = BitVec.ofNat 64 value) :
    WP isa (.block (Checks.widthMask n)) s fun t =>
      t.gpr .x15 = mask (decide (value = n)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x7, .x15] s t := by
  have hn64 : n < 2 ^ 64 := by omega
  have he : (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0 ↔ value = n := by
    change (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0#64 ↔ value = n
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hn64] using h'
    · intro h; rw [h]
  have hz : BitVec.setWidth 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  unfold Checks.widthMask
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun u =>
    u.gpr .x3 = BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hu3, hum⟩, hku⟩ => ?_
  · brun [h8, hz]
  refine WP.mono (zeroMask_ok u) fun t ⟨⟨ht, _, _, htm⟩, hkt⟩ =>
    ⟨by rw [ht, hu3]; exact congrArg mask (decide_eq_decide.mpr he), htm.trans hum,
      (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
