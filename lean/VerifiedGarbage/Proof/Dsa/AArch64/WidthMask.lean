module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Equality masks for supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem widthMask_ok {s : State} {n value : Nat}
    (hn : n < 2 ^ 16) (hv : value < 2 ^ 64) (h8 : s.gpr .x8 = BitVec.ofNat 64 value) :
    WP isa (.block (Checks.widthMask n)) s fun t =>
      t.gpr .x3 = mask (decide (value = n)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  have hn64 : n < 2 ^ 64 := by omega
  have he : (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0 ↔ value = n := by
    change (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0#64 ↔ value = n
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hn64] using h'
    · intro h; rw [h]
  unfold Checks.widthMask
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
    u.gpr .x3 = BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hu, hm⟩, hk⟩ => ?_
  · have hn' : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    brun [h8, hn']
  refine WP.mono (zeroMask_ok .x3 false) fun t ⟨ht, htm, hkt⟩ => ?_
  simp only [Bool.false_eq_true, ite_false, hu, decide_eq_decide.mpr he] at ht
  exact ⟨ht, htm.trans hm, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
