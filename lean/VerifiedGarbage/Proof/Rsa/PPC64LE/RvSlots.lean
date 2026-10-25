module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-!
# `vg_rsa_recover_primes` on PPC64LE: slots and flags

The slots of the header as numbers, flags (0 or 1) as words (`b64`), and
the top bit of a difference as a comparison (`lt64`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A slot apart from a store. -/
theorem slot_wne (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) : slot (m.writeW (off B d) v) B e = slot m B e := by
  simp only [slot, w32, off]
  rw [Mem.readW_writeW_sep (Offset.sep B (h.symm) he hd) (by decide)]

/-- A slot loaded. -/
theorem ld_slot {m : Mem} {B : Addr} {d v : Nat} (h : slot m B d = v) :
    (m.readW (B + BitVec.ofNat 64 d) 32).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have := (m.readW (B + BitVec.ofNat 64 d) 32).isLt
  simp only [slot, w32, off] at h
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), h]
  rw [← h]; omega

/-- A flag as a word. -/
abbrev b64 (b : Bool) : BitVec 64 := BitVec.ofNat 64 (b2n b)

theorem b64_or (a b : Bool) : b64 a ||| b64 b = b64 (a || b) := by cases a <;> cases b <;> decide

theorem b64_w32 (b : Bool) : (b64 b).setWidth 32 = BitVec.ofNat 32 (b2n b) := by cases b <;> decide

theorem b2n_ite (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  by_cases h : p <;> simp [h, b2n]

/-- The top bit of `a - b`: `a < b`. -/
theorem lt64 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = b64 (decide (a < b)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega)]
  by_cases h : a < b
  · simp only [h, decide_true, b2n, ite_true]; omega
  · simp only [h, decide_false, b2n, Bool.false_eq_true, ite_false]; omega

end VG.Proof.Rsa.PPC64LE.Recover
